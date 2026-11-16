-- Prove2me | Theorems.Thm_ARGFContract_Hardness_Supplement_theorem_3
-- name    : ARGFContract.Hardness.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:03:56.223219+00:00
-- url     : https://prove2.me/theorems/a4d67910-0cc8-47a7-be87-24f09167d215
-- title:
--   Theorem 3 (companion theorem; not used in the proof of the goal) — Algorithm 2: cost-bucket profile enumeration
-- statement:
--   Let $E=\{1,\dots,N\}$ be agents with competencies $p_i\in\mathbb R$ and costs $c_i\ge0$, let $f$ be an ARGF (Definition 2.1) whose evaluation on an $m$-set takes at most $D(m+1)^{K_f}$ time, and suppose all costs lie in an interval of length at most $1$, i.e. $c_i-c_j\le1$ for all $i,j$. Let $B=\{B_1,\dots,B_\ell\}$ be a partition of $E$ into nonempty buckets which is an $\epsilon$-cost-bucket partition ($\epsilon\ge0$) and $\delta$-separated ($\delta>0$) in the sense of Assumption 3.1.
--
--   **Algorithm 2** sorts each bucket by non-increasing competency, evaluates $\mu(Q_C(x))$ for every profile $x\in\{0,\dots,|B_1|\}\times\dots\times\{0,\dots,|B_\ell|\}$, and returns a maximizer $\hat S_C$. There are an absolute constant $A$ and one program which, for every $K_f$ and $D$, with a constant $C$ depending only on $K_f$ and $D$, implements Algorithm 2 in time
--
--   $$C\,(N+2)^{k+K_f},\qquad k=\lceil A(1+1/\delta)\rceil ,$$
--
--   and its output satisfies, for every optimal committee $S_{OPT}$,
--
--   $$\mu(\hat S_C)\ \ge\ \mu(S_{OPT})-\epsilon\,|S_{OPT}| .$$
--
--   Consequently, if $\epsilon|S_{OPT}|\le\beta\,\mu(S_{OPT})$ for some $\beta\in(0,1)$, then $\mu(\hat S_C)\ge(1-\beta)\,\mu(S_{OPT})$.
--
--   The theorem turns similar costs into an additive approximation whose running time is polynomial for every fixed separation $\delta$.
--
--   **Formalization Note** Running time is measured in the value-oracle real RAM of `OracleMachine`, counting executed instructions plus oracle time. The program receives costs, competencies and bucket labels, not $\epsilon$ or $\delta$. Competency ties inside a bucket are broken by agent index.
--
--   Differences from the source:
--   - encoding: running time of an offline algorithm with value oracle f (Definition 2.1(3): an evaluation costs O(|S|^{K_f})) → one uniform admissible program of the value-oracle real RAM (published SmaleNinth core plus integer memory, one-agent committee edits and a query instruction); time = executed instructions plus the oracle time τ(|S|) of every query; reason: unit-cost real arithmetic and comparisons with no sort, maximum or set-scan primitive; the oracle is charged per query as in Definition 2.1(3)
--   - encoding: O(N^{k+K_f}) with k ∈ O(1+1/δ) → C·(N+2)^{⌈A(1+1/δ)⌉+K_f} with an absolute A and C depending only on K_f and the oracle coefficient D (τ(m) ≤ D(m+1)^{K_f}); reason: base N+2 avoids the degenerate N∈{0,1}; for N≥2, (N+2)^k ≤ N^{2k}, so the exponent stays O(1+1/δ)
--   - reading: the proof's 'all active costs lie in an interval of length R_c ≤ 1' (p. 15) → hypothesis c_i − c_j ≤ 1 for all agents; reason: the bucket bound ℓ ≤ 1+1/δ and hence the runtime rest on it; nonnegative costs alone do not give it
--   - encoding: Algorithm 2 returns Ŝ_C ∈ argmax_x µ(Q_C(x)) after sorting each bucket by competency → the output is Q_C(x) for a profile x maximizing µ(Q_C(·)) over all profiles; ties in competency broken by agent index; reason: a deterministic tie order fixes Q_C; argmax ties are arbitrary as in the source
--   - encoding: partition B = {B_1,…,B_ℓ} of E → a surjective labelling B : Fin N → Fin ℓ; reason: blocks of a partition are nonempty; same instances
--   - encoding: δ-separated, δ not otherwise constrained in the statement → hypothesis 0 < δ; reason: the runtime exponent k ∈ O(1 + 1/δ) is undefined at δ = 0 and δ-separation is vacuous for δ ≤ 0; only undefined cases are excluded
--   - encoding: S_OPT, an optimal committee → every set Sopt with IsOptimalSet f c Sopt; reason: the bound is asserted for every maximizer, in particular the one the source names
--   - generalization: E is the pruned ground set returned by Algorithm 1 (p. 10, 'throughout the remainder of the paper') → no pruning hypothesis (p_i − c_i > 0 is not assumed); reason: the statement holds on every ground set; the pruned instances are a special case
-- source:
--   Jalal Etesami, Larkin Liu, Rilind Sahitaj, STOC 2027 submission #348 (October 2026), Theorem 3, p. 14 (proof pp. 14–15)

import Mathlib
import Definitions.Def_ARGFContract_Hardness_ARGF
import Definitions.Def_ARGFContract_Hardness_Supplement_Prefixes
import Definitions.Def_ARGFContract_Hardness_Supplement_OracleMachine

open Finset

namespace ARGFContract.Hardness.Supplement

/-- Theorem 3, pp. 14–15 (Algorithm 2). One uniform program, given costs, competencies and
the bucket labels, returns the best competency prefix `Q_C(x)` over all profiles `x`, within
`C (N+2)^(k + K_f)` time units with `k = ⌈A (1 + 1/δ)⌉`, whenever the oracle costs at most
`D (m+1)^{K_f}` on an `m`-set; every optimal `S_OPT` then satisfies the additive bound, and
the conditional `(1 − β)` bound for every `β ∈ (0,1)`. The costs lie in an interval of
length at most one (the active-cost range used in the proof, p. 15). -/
theorem theorem_3 :
    ∃ P : OracleProgram, Admissible P ∧ ∃ A : ℕ, ∀ Kf Dτ : ℕ, ∃ C : ℕ,
      ∀ (n ℓ : ℕ) (p c : Fin n → ℝ) (f : Finset (Fin n) → ℝ) (τ : ℕ → ℕ)
        (B : Fin n → Fin ℓ) (ε δ : ℝ),
        ARGFContract.Hardness.IsARGF p f → (∀ i, 0 ≤ c i) →
        (∀ m, τ m ≤ Dτ * (m + 1) ^ Kf) →
        0 ≤ ε → 0 < δ → Function.Surjective B →
        IsCostBucketPartition c B ε → IsSeparated c B δ →
        (∀ i j, c i - c j ≤ 1) →
        RunsWithin P f τ (initState n (encodeReals c p) (encodeInts ℓ (fun i => (B i : ℕ))))
          (C * (n + 2) ^ (⌈(A : ℝ) * (1 + 1 / δ)⌉₊ + Kf))
          (fun S _ _ =>
            (∃ x ∈ profiles B, S = competencyPrefixSet p B x ∧
              ∀ y ∈ profiles B,
                netUtilityReal f c (competencyPrefixSet p B y) ≤ netUtilityReal f c S) ∧
            ∀ Sopt : Finset (Fin n), IsOptimalSet f c Sopt →
              netUtilityReal f c Sopt - ε * Sopt.card ≤ netUtilityReal f c S ∧
              ∀ β : ℝ, 0 < β → β < 1 →
                ε * Sopt.card ≤ β * netUtilityReal f c Sopt →
                (1 - β) * netUtilityReal f c Sopt ≤ netUtilityReal f c S) := by sorry

end ARGFContract.Hardness.Supplement
