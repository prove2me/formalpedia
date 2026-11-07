-- Prove2me | Theorems.Thm_BoolCSPDel_theorem_1_1
-- name    : BoolCSPDel.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:56:26.928297+00:00
-- url     : https://prove2.me/theorems/8e7b12a4-3004-4a09-b59f-f4f3345a6b2f
-- title:
--   Theorem 1.1 — strict-turnstile $\mathrm{CSP}(\Gamma)$ takes $\tilde O_k(n^d)$ and $\Omega_k(n^d/\log n)$ bits, with exact sparsifiers
-- statement:
--   Let $\Gamma$ range over languages of nonempty proper Boolean relations of arity at most $k$, and $d=\deg_{\mathbb Z}(\Gamma)$.
--
--   1. **Upper bound.** For every nonempty $\Gamma$ there is one finite program such that, for all $n,\mu\ge1$, $\delta=1/M$ with $M\ge3$, and every strict-turnstile stream with prefix multiplicities at most $\mu$, on every coin tape the program halts within
--
--   $$C\,n^d\log^K(2+2n\mu/\delta)$$
--
--   cells, leaving an answer and at most that many constraints. With probability at least $1-\delta$, the answer decides satisfiability of the final instance and the constraints form an exact sparsifier of it. Here $K$ is absolute and $C$ depends on $k$.
--
--   2. **Lower bound for decisions.** If $\Gamma$ is not constant-satisfiable, every one-pass algorithm deciding $\mathrm{CSP}(\Gamma)$ with probability at least $2/3$ on each strict-turnstile stream of length at most $n^{c_s}$ has at least $cn^d/\log n$ bits of memory, for all $n\ge N_0$.
--
--   3. **Lower bound for sparsification.** If $\Gamma$ is nonempty, possibly constant-satisfiable, the same bound holds for every algorithm returning an exact sparsifier with probability at least $2/3$.
--
--   The constants $c,c_s,N_0$ depend on $k$ only. The integer capturing degree therefore determines the space complexity up to polylogarithmic factors.
--
--   **Formalization Note** The upper bound counts the input's parsing, seeds, output and decoding workspace on a one-tape machine with one-way input and coins. The lower bounds hold for any automaton on each $n$ with a free persistent seed and memory $\log_2|S|$.
--
--   Differences from the source:
--   - reading: "using … bits", no machine named → cells visited on the program of Program, one finite program for each Γ, with no oracle, halting within the bound on every coin tape; reason: p.17 counts "all retained memory, including decoding workspace"; pp.33, 55 count stored randomness, output, working space for every choice of seeds
--   - reading: "requires … bits", no model named → any automaton for each n with a free persistent seed, memory log₂|S|; reason: the most general reasonable class; it contains the machine of the upper clause
--   - generalization: error 1/3 and polynomially bounded stream lengths, nontrivial Γ, in the upper bound → every δ = 1/M, stream of any length with prefix multiplicities at most μ, and Γ possibly constant-satisfiable; reason: this is Corollary 5.10; at δ = 1/3 and length n^c it has μ ≤ n^c and the logarithm is at most (c + 3) log(n + 2) up to a constant
--   - generalization: polylog of a fixed power, with constants from k; the sparsifier stated separately → K absolute, chosen before k; one event of failure covers the answer and the sparsifier together; the list length holds on every coin tape; reason: §A.1.3 and Lemma A.4 give a fixed power of log Q with O_{b0} constants; the proof of Theorem 5.1 computes the answer from S; the printed statement follows
--   - generalization: common arity after padding, in the paper's general setting → arity at most k, each relation its own; reason: p.21 and Corollary 4.16; padding is a special case
--   - encoding: O_k and Ω_k for a fixed Γ → C, c, c_s, N₀ chosen for k before Γ; reason: finitely many languages of arity at most k (p.17)
--   - encoding: 0 < δ < 1/2 → δ = 1/M, M ≥ 3; reason: any real δ has M = ⌈1/δ⌉ with δ/2 ≤ 1/M ≤ δ; the bound moves by a constant
--   - encoding: a subset S of active constraints → a list S, read as S.toFinset, with its length bounded; reason: the output must be written on the tape; the bound on the length covers the set
--   - encoding: success with probability at least 2/3 → CosDensity.SucceedsWP: a measurable event of measure at least 2/3 inside the success set; reason: an inner-measure lower bound; for measurable success sets it is the same
--   - encoding: the empty language excluded implicitly → Γ.Nonempty in the upper and sparsification clauses; ¬ConstSat implies it in the decision clause; reason: Corollaries 5.10 and 4.16 say nonempty
--   - encoding: O_k(n^d polylog n) and Ω_k(n^d/ log n), asymptotic in n → the upper bound for every n ≥ 1, the lower bounds for every n ≥ N₀ with N₀ ≥ 2; reason: at n = 0 the bound C·0^d is 0 while every run visits a cell, and log n > 0 needs n ≥ 2; the asymptotic statements are unchanged
-- source:
--   Bandekar, Sharma, Velusamy, A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions, STOC 2027 submission (manuscript sha256 15f83519…), Theorem 1.1 and footnote 4, p.6; Corollaries 5.10, p.37, 4.15, p.28, 4.16, p.29

import Mathlib
import Definitions.Def_BoolCSPDel_degZ
import Definitions.Def_BoolCSPDel_TurnstileAlg
import Definitions.Def_BoolCSPDel_inputWord
import Definitions.Def_CosDensity_StreamAlg

open MeasureTheory

namespace BoolCSPDel

/-- **Theorem 1.1 (main result).** Bandekar, Sharma, Velusamy, *A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions*, STOC 2027 submission (manuscript sha256 15f83519…), Theorem 1.1 and footnote 4, p.6, in the explicit forms of Corollaries
5.10, 4.15 and 4.16, pp.37, 28, 29.

`d = deg_ℤ(Γ)` throughout, and `Γ` ranges over languages of nonempty proper relations of arity at most `k`.

(U) For every nonempty `Γ`, one finite coin-flipping program solves, for all `n, μ ≥ 1` and `M ≥ 3` and every legal
stream with prefix multiplicities at most `μ`, both problems at once: on every coin tape it halts within
`C n^d polylog(2nμ/δ)` cells, with `δ = 1/M`, leaving an answer and at most that many constraints; off an event of
probability at most `δ`, the answer decides satisfiability of the final instance and the constraints are an exact
sparsifier of it.

(L₁) For `Γ` not constant-satisfiable, every algorithm correct with probability `2/3` on each legal stream of length
at most `n^{c_s}` has at least `c n^d / log n` bits of memory, for all `n ≥ N₀`.

(L₂) For every nonempty `Γ`, the same bound for algorithms returning an exact sparsifier with probability `2/3`.

**Formalization Note.** (U) counts input parsing, seeds, output and decoding workspace, on the machine of
`Program`: nothing is free. (L₁), (L₂) allow any automaton on each `n` with a free persistent seed. Each bound has
`K` (absolute) and `C`, `c`, `c_s`, `N₀` (from `k`) before `Γ`. Every stream length is allowed in (U), with only the
multiplicities bounded. At `δ = 1/3` and polynomially long streams (U) is the bound printed in Theorem 1.1. -/
theorem theorem_1_1 :
    (∃ K : ℕ, ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ Γ : Lang k, Γ.Nonempty → AllNonemptyProper Γ →
      ∃ Pg : Program, OracleFree Pg ∧
        ∀ (n μ M : ℕ), 1 ≤ n → 1 ≤ μ → 3 ≤ M → ∀ s : List (Con Γ (Fin n) × Bool),
          IsLegal s → BoundedBy μ s →
          let word := inputWord Γ n μ M s
          let Bnd : ℝ := C * (n : ℝ) ^ degZLang Γ * polylog K (2 * n * μ * M)
          (∀ coins : ℕ → Bool, ∃ cfg, HaltsWith Pg noOracle word coins cfg ∧ (cfg.space : ℝ) ≤ Bnd ∧
            ∃ (a : Bool) (S : List (Con Γ (Fin n))),
              TapeHolds cfg.tape 0 (outWord Γ n a S) ∧ (S.length : ℝ) ≤ Bnd) ∧
          coinMeasure {coins | ¬ ∃ cfg, HaltsWith Pg noOracle word coins cfg ∧
            ∃ (a : Bool) (S : List (Con Γ (Fin n))), TapeHolds cfg.tape 0 (outWord Γ n a S) ∧
              (a = true ↔ (Sat (freq s)).Nonempty) ∧ IsExactSparsifier S.toFinset (freq s)} ≤
            ENNReal.ofReal (1 / M)) ∧
    (∀ k : ℕ, ∃ (c : ℝ) (c_s N₀ : ℕ), 0 < c ∧ 2 ≤ N₀ ∧
      ∀ Γ : Lang k, AllNonemptyProper Γ → ¬ ConstSat Γ → ∀ n, N₀ ≤ n →
        ∀ (Ω St : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] [Fintype St]
          (A : TurnstileAlg (Con Γ (Fin n)) Ω St Bool),
          (∀ s : List (Con Γ (Fin n) × Bool), IsLegal s → s.length ≤ n ^ c_s →
            CosDensity.SucceedsWP μ
              (fun ω => A.out ω (A.run ω s) = true ↔ (Sat (freq s)).Nonempty) (2 / 3)) →
          c * (n : ℝ) ^ degZLang Γ / Real.log n ≤ CosDensity.memoryBits St) ∧
    (∀ k : ℕ, ∃ (c : ℝ) (c_s N₀ : ℕ), 0 < c ∧ 2 ≤ N₀ ∧
      ∀ Γ : Lang k, Γ.Nonempty → AllNonemptyProper Γ → ∀ n, N₀ ≤ n →
        ∀ (Ω St : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] [Fintype St]
          (A : TurnstileAlg (Con Γ (Fin n)) Ω St (Finset (Con Γ (Fin n)))),
          (∀ s : List (Con Γ (Fin n) × Bool), IsLegal s → s.length ≤ n ^ c_s →
            CosDensity.SucceedsWP μ
              (fun ω => IsExactSparsifier (A.out ω (A.run ω s)) (freq s)) (2 / 3)) →
          c * (n : ℝ) ^ degZLang Γ / Real.log n ≤ CosDensity.memoryBits St) := by sorry

end BoolCSPDel
