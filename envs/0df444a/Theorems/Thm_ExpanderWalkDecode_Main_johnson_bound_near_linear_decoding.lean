-- Prove2me | Theorems.Thm_ExpanderWalkDecode_Main_johnson_bound_near_linear_decoding
-- name    : ExpanderWalkDecode.Main.johnson_bound_near_linear_decoding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:22:49.707851+00:00
-- url     : https://prove2.me/theorems/c35ca7a6-ca99-46bd-8ddd-684fe3a3e798
-- title:
--   Theorem 1.1 — binary linear codes of bias $\varepsilon$ and rate $\Omega(\varepsilon^{2+\beta})$ list decodable up to $2\sqrt\varepsilon$ in time $\tilde O(N)(1/\varepsilon)^{c_\beta}$
-- statement:
--   There are absolute constants $b>0$ and $p$ such that for every $0<\beta\le1/2$ there are constants $c_\beta\le(1/\beta)^{b/\beta}$, $K_\beta$ and $\kappa_\beta>0$ with the following property. For every $\varepsilon>0$ there is an explicit family of binary linear codes $C^{(N)}\subseteq\mathbb F_2^N$, one of every blocklength $N$, and one randomized program, such that
--
--   1. every $C^{(N)}$ has bias at most $\varepsilon$;
--   2. $\mathrm{rate}(C^{(N)})\ge\kappa_\beta\min(\varepsilon,1)^{2+\beta}$ for all $N\ge N_0(\varepsilon)$;
--   3. for every $N\ge1$, every $\rho\ge2\sqrt\varepsilon$ and every received word $Y$, the program, run on $(N,\rho,Y)$, halts within
--   $$K_\beta\,N\,(\log_2(N+2))^p\,(1+1/\varepsilon)^{c_\beta}=\tilde O(N)\cdot(1/\varepsilon)^{c_\beta}$$
--   steps and outputs exactly $\mathrm{LIST}(Y,\rho)=\{X\in C^{(N)}:\langle Y,X\rangle\ge\rho\}$ with probability at least $1/8$.
--
--   A second admissible program outputs a spanning generator matrix for every $C^{(N)}$ within $K_g(N+1)^{K_g}$ units of work, where $K_g>0$ may depend on $\varepsilon,\beta$.
--
--   So the codes approach the Gilbert–Varshamov rate $\varepsilon^{2}$ up to $\varepsilon^{\beta}$ and are list decodable up to the Johnson radius $2\sqrt\varepsilon$, in time near-linear in the blocklength and polynomial in $1/\varepsilon$ for fixed $\beta$.
--
--   Differences from the source:
--   - reading: a family {C^(N)}_{N∈ℕ} (Theorem 1: {C_k}_{k∈ℕ}, time Õ(k)) → one code of every blocklength N; bias for every N; the rate bound for N ≥ N₀(ε); time in N; reason: the stronger exact-blocklength reading of the introduction's family; an asymptotic rate is an eventual bound
--   - reading: Ct is ρ-list-decodable in time T (Definition 1: an efficient randomized algorithm, constant success probability) → one program for the whole family (given ε, β), input (N, ρ, Y), worst-case time on the machine of this mission, success probability ≥ 1/8; reason: a per-code algorithm could be a lookup table; 1/8 is the probability of Theorem 1 (Restated)
--   - reading: bias ε → every nonzero codeword has |sign average| ≤ ε; reason: the small-bias reading used by the paper's correlation arguments; it implies the ε-balanced distance condition of §1
--   - encoding: rate Ω(ε^{2+β}), time Õ(N)·(1/ε)^{c_β}, c_β = (1/β)^{O(1/β)} → ∃ absolute b, p; for each β: c_β ≤ (1/β)^{b/β}, K_β, κ_β > 0; rate ≥ κ_β min(ε,1)^{2+β}; time ≤ K_β N (log₂(N+2))^p (1+1/ε)^{c_β}; reason: unfolding of the asymptotic notation with constants chosen before ε, N, ρ, Y; min and 1+1/ε change only constants for ε ≥ 1/2
--   - encoding: Y ∈ {±1}^N; N ∈ ℕ → Y ∈ F_2^N via signs; decoding for N ≥ 1; reason: same words; at N = 0 there is no coordinate
--   - reading: the explicit expander-walk construction of §4 → a program constructs a spanning generator matrix in polynomial time; reason: explicitness must be a conclusion; the decoder is quantified existentially, as Theorem 1 asserts that a decoding algorithm exists
--   - reading: algorithmic running time, without an explicit machine specification → the mission machine: a unit-cost real RAM with √, natural logarithm, fair coins and an exact symmetric eigendecomposition charged d³+1; reason: the source thresholds eigenvalues exactly (Figure 3), takes exact top eigenvectors (Figure 4) and sets parameters by logarithmic formulas (Δ, ℓ), counting these steps as polynomial work; an exact eigenvalue threshold is meaningful only in exact real arithmetic, so this is the model the source computes in; the cubic charge is one polynomial cost for the step the source calls immediate
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), p. 3 (PDF p. 6), §1.1, Theorem 1.1; Theorem 1 (Main), p. 11 (PDF p. 14); Theorem 1 (Restated), p. 18 (PDF p. 21)

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_Codes

namespace ExpanderWalkDecode.Main

open scoped Matrix

/-- Theorem 1.1 (p. 3) = Theorem 1 (Main) (p. 11), with the guarantee of Theorem 1 (Restated)
(p. 18): there are absolute constants `b > 0` and `p` such that for every `0 < β ≤ 1/2` there are
`c_β ≤ (1/β)^{b/β}`, `K_β` and `κ_β > 0` with the following property. For every `ε > 0` there is a
explicit family of binary linear codes `C^{(N)}`, one of every blocklength `N`, each with bias at most `ε`,
with rate at least `κ_β min(ε, 1)^{2+β}` for all large `N`, and one randomized program that, for
every `N ≥ 1`, every `ρ ≥ 2√ε` and every received word, halts within
`K_β N (log₂(N+2))^p (1 + 1/ε)^{c_β}` steps and outputs exactly `LIST(Y, ρ)` with probability at
least `1/8`. A second program constructs a generator matrix in polynomial time. -/
theorem johnson_bound_near_linear_decoding :
    ∃ (b : ℝ) (p : ℕ), 0 < b ∧
      ∀ β : ℝ, 0 < β → β ≤ 1 / 2 →
        ∃ (c K κ : ℝ), 0 < c ∧ c ≤ (1 / β) ^ (b / β) ∧ 0 < κ ∧
          ∀ ε : ℝ, 0 < ε →
            ∃ (C : ∀ N : ℕ, BinaryLinearCode N) (P Pgen : Program) (Kg : ℝ) (N₀ : ℕ),
              Admissible P ∧ Admissible Pgen ∧ 0 < Kg ∧
              (∀ N : ℕ, HasBias (C N) ε) ∧
              (∀ N : ℕ, N₀ ≤ N → κ * (min ε 1) ^ (2 + β) ≤ rate (C N)) ∧
              (∀ N : ℕ, RunsWithin Pgen (natInput N) (Kg * ((N : ℝ) + 1) ^ Kg)
                (fun out => EncodesGenerator out (C N)) 1) ∧
              ∀ N : ℕ, 1 ≤ N → ∀ ρ : ℝ, 2 * Real.sqrt ε ≤ ρ →
                ListDecodesWithin P C ρ N
                  (K * N * Real.logb 2 ((N : ℝ) + 2) ^ p * (1 + 1 / ε) ^ c) (1 / 8) := by sorry

end ExpanderWalkDecode.Main
