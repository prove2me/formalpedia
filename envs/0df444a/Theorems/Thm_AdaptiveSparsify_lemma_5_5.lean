-- Prove2me | Theorems.Thm_AdaptiveSparsify_lemma_5_5
-- name    : AdaptiveSparsify.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:49:41.42038+00:00
-- url     : https://prove2.me/theorems/da8703fb-36b6-45f4-84af-35314703773e
-- title:
--   Lemma 5.5 (corrected: initial estimates carry the margin $d/n$) — the checker\'s estimates are overestimates
-- statement:
--   Consider the checker-induced estimates of Definition 5.4 against an adaptive halving strategy, starting from $\tilde\tau^{(0)}_i\ge d/n+a_i^\top(A^\top A+I/\kappa)^{-1}a_i$. With high probability, for every $q$ with $1\le q<n$ such that the sets played through $q$ form a batched halving sequence, and for every row $i$,
--
--   $$\tilde\tau^{(q)}_i\ge(a^{(q)}_i)^\top\big((A^{(q)})^\top A^{(q)}+I/\kappa\big)^{-1}a^{(q)}_i.$$
--
--   The estimates remain valid even though the rows halved depend on previously published estimates.
--
--   Differences from the source:
--   - correction: τ̃^{(0)} is the overestimate of Lemma 2.4 → τ̃^{(0)}_i ≥ d/n + the leverage of a_i against G^{(0)}; reason: as printed Lemma 5.5 fails: d = 1, n = 2, κ = 100, a = (0.05, 1), H^{(1)} = {2}, τ̃^{(0)} exact gives τ₁^{(0)} = 0.00247 and τ₁^{(1)} = 0.00952, while a₁⊤Δa₁ ≈ 0.0071 stays below the threshold d/(10 n log n), so row 1 is never recomputed and τ̃₁^{(1)} < τ₁^{(1)}; the proof uses the margin d/n
--   - generalization: Definition 5.4 assumes every row is halved at most O(log n) times → no bound on the number of halvings of a row; reason: the proof does not use it; the statement specializes to the printed one under the assumption
--   - reading: ϵ_checker = 0.001/(C d log(ndκ)), O(log n) JL rows, O(ϵ⁻² log n) sampling rate → ϵ_checker = 0.001/(C (d log(n + d + κ + 2) + 1)), ⌈C_jl log n⌉ rows, T = ⌈C_s ϵ⁻² log n Στ̃⌉ draws, with C, C_s, C_jl chosen after c and before the instance; reason: log(ndκ) vanishes at n = d = κ = 1; the page leaves the constants hidden
--   - reading: G̃^{(0)} in step 4(a) at q̂ = 0, undefined since steps start at q = 1 → G̃^{(0)} = G^{(0)}; reason: the natural reading
--   - reading: the sequence of row halvings, with Q < n and the conditions of Definition 5.2 → the sets are played by a measurable adaptive strategy from the history of τ̃, and the bad event at q looks only at tapes on which the play through q is a batched halving sequence and q < n; reason: the adversary is adaptive (p.37); a play that breaks the conditions on some tapes does not make the event vacuous on the others
--   - reading: "With high probability" → failure at most (n + 2)^{−c} for every c > 0, with the constants chosen after c; reason: the constants of Lemma 2.1 and Lemma 2.3 scale; base n + 2 avoids a vacuous bound at small n
--   - reading: hypotheses of Lemma 5.3 implicit in the constant of Definition 5.4 → ‖a_i‖² ≤ κ, κ ≥ 1, n ≥ 2, d ≥ 1; reason: step 1 uses the constant of Lemma 5.3, and log n > 0 is needed in the threshold
-- source:
--   Liu, Peng, Tang, Weng, Yang, Adaptive Matrix Sparsification with Applications to Empirical Risk Minimization and Computational Geometry (manuscript, sha256 7a66a27b…), Definition 5.4, pp.35–36; Lemma 5.5, p.36

import Mathlib
import Definitions.Def_AdaptiveSparsify_Checker

open Matrix

namespace AdaptiveSparsify

/-- **Lemma 5.5**, p.36 (corrected: C4).

Liu, Peng, Tang, Weng, Yang, *Adaptive Matrix Sparsification …* (manuscript, sha256 7a66a27b…), Definition 5.4, pp.35–36, Lemma 5.5, p.36.

"With high probability, after each batch 1 ≤ q ≤ Q, τ̃_i^{(q)} ≥ (a_i^{(q)})⊤((A^{(q)})⊤A^{(q)} + I/κ)⁻¹a_i^{(q)}
∀q, i"

**Formalization Note.** The process is `checkerRun` against any measurable adaptive halving strategy.
Correction C4: `τ̃^{(0)}` is `d/n` plus an overestimate of the initial leverage (`InitialEstimates`). The sets
form a batched halving sequence and `q < n`, as Definition 5.4 assumes; this binds along the run, so the bad
event at `q` only looks at tapes on which the play through `q` meets it. Definition 5.4's "every row is halved
for at most O(log n) times" is not needed and is dropped. Failure is at most `(n + 2)^{-c}` for every `c`, with
the constants chosen after `c` and before the instance. -/
theorem lemma_5_5 : ∀ c : ℝ, 0 < c → ∃ C : CheckerConstants, 0 < C.Clem ∧ 0 < C.Cs ∧ 0 < C.Cjl ∧
    ∀ (n d : ℕ) (i₀ : Fin n) (A : Matrix (Fin n) (Fin d) ℝ) (κ : ℝ) (τ0 : Fin n → ℝ)
      (σ : HalvingStrategy n),
      2 ≤ n → 1 ≤ d → 1 ≤ κ → (∀ i, A i ⬝ᵥ A i ≤ κ) → InitialEstimates κ A τ0 → σ.Measurable →
      checkerTape {ω | ∃ q : ℕ, 1 ≤ q ∧ q < n ∧
          IsBatchedHalving κ A (playedSets C i₀ κ A τ0 σ ω) q ∧
          ∃ i, (checkerRun C i₀ κ A τ0 σ ω q).τ i <
            leverage (gramOf κ (checkerRun C i₀ κ A τ0 σ ω q).A)
              ((checkerRun C i₀ κ A τ0 σ ω q).A i)} ≤
        ENNReal.ofReal (((n : ℝ) + 2) ^ (-c)) := by sorry

end AdaptiveSparsify
