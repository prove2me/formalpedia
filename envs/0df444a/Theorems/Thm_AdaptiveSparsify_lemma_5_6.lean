-- Prove2me | Theorems.Thm_AdaptiveSparsify_lemma_5_6
-- name    : AdaptiveSparsify.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:48:55.873636+00:00
-- url     : https://prove2.me/theorems/6c45189d-7fe7-4ba5-980f-ab4cf8f04c12
-- title:
--   Lemma 5.6 (corrected: adds $\sum_i\tilde\tau^{(0)}_i$ to $22d$) — the checker\'s estimates sum to $O(d)$ plus their initial sum
-- statement:
--   In the setting of Lemma 5.5, with high probability, for every $q$ with $1\le q<n$ such that the sets played through $q$ form a batched halving sequence,
--
--   $$\sum_i\tilde\tau^{(q)}_i\le22d+\sum_i\tilde\tau^{(0)}_i.$$
--
--   Together with the initial sum $O(d\log d)$ of Lemma 2.4, the estimates stay $\tilde O(d)$, so sampling by them gives a small sparsifier.
--
--   Differences from the source:
--   - correction: Σ_i τ̃^{(q)}_i ≤ 22d → Σ_i τ̃^{(q)}_i ≤ 22d + Σ_i τ̃^{(0)}_i; reason: the printed proof treats only recomputed rows; a row never recomputed keeps τ̃^{(0)}, whose sum Lemma 2.4 bounds only by O(d log d), so 22d can fail
--   - correction: τ̃^{(0)} is the overestimate of Lemma 2.4 → τ̃^{(0)}_i ≥ d/n + the leverage of a_i against G^{(0)}; reason: the same correction as Lemma 5.5, so that both lemmas speak of one process
--   - generalization: Definition 5.4 assumes every row is halved at most O(log n) times → no bound on the number of halvings of a row; reason: the proof does not use it; the statement specializes to the printed one under the assumption
--   - reading: ϵ_checker = 0.001/(C d log(ndκ)), O(log n) JL rows, O(ϵ⁻² log n) sampling rate → ϵ_checker = 0.001/(C (d log(n + d + κ + 2) + 1)), ⌈C_jl log n⌉ rows, T = ⌈C_s ϵ⁻² log n Στ̃⌉ draws, with C, C_s, C_jl chosen after c and before the instance; reason: log(ndκ) vanishes at n = d = κ = 1; the page leaves the constants hidden
--   - reading: G̃^{(0)} in step 4(a) at q̂ = 0, undefined since steps start at q = 1 → G̃^{(0)} = G^{(0)}; reason: the natural reading
--   - reading: the sequence of row halvings, with Q < n and the conditions of Definition 5.2 → the sets are played by a measurable adaptive strategy from the history of τ̃, and the bad event at q looks only at tapes on which the play through q is a batched halving sequence and q < n; reason: the adversary is adaptive (p.37); a play that breaks the conditions on some tapes does not make the event vacuous on the others
--   - reading: "With high probability" → failure at most (n + 2)^{−c} for every c > 0, with the constants chosen after c; reason: the constants of Lemma 2.1 and Lemma 2.3 scale; base n + 2 avoids a vacuous bound at small n
--   - reading: hypotheses of Lemma 5.3 implicit in the constant of Definition 5.4 → ‖a_i‖² ≤ κ, κ ≥ 1, n ≥ 2, d ≥ 1; reason: step 1 uses the constant of Lemma 5.3, and log n > 0 is needed in the threshold
-- source:
--   Liu, Peng, Tang, Weng, Yang, Adaptive Matrix Sparsification with Applications to Empirical Risk Minimization and Computational Geometry (manuscript, sha256 7a66a27b…), Definition 5.4, pp.35–36; Lemma 5.6, p.37

import Mathlib
import Definitions.Def_AdaptiveSparsify_Checker

open Matrix

namespace AdaptiveSparsify

/-- **Lemma 5.6**, p.37 (corrected: C4).

Liu, Peng, Tang, Weng, Yang, *Adaptive Matrix Sparsification …* (manuscript, sha256 7a66a27b…), Definition 5.4, pp.35–36, Lemma 5.6, p.37.

"With high probability, ∑_i τ̃_i^{(q)} ≤ 22d for every q."

**Formalization Note.** Correction C4: the printed proof treats only recomputed rows, and a row never
recomputed keeps `τ̃^{(0)}`, so the bound is `22d + ∑_i τ̃_i^{(0)}`. The process and its conventions are those of
Lemma 5.5. -/
theorem lemma_5_6 : ∀ c : ℝ, 0 < c → ∃ C : CheckerConstants, 0 < C.Clem ∧ 0 < C.Cs ∧ 0 < C.Cjl ∧
    ∀ (n d : ℕ) (i₀ : Fin n) (A : Matrix (Fin n) (Fin d) ℝ) (κ : ℝ) (τ0 : Fin n → ℝ)
      (σ : HalvingStrategy n),
      2 ≤ n → 1 ≤ d → 1 ≤ κ → (∀ i, A i ⬝ᵥ A i ≤ κ) → InitialEstimates κ A τ0 → σ.Measurable →
      checkerTape {ω | ∃ q : ℕ, 1 ≤ q ∧ q < n ∧
          IsBatchedHalving κ A (playedSets C i₀ κ A τ0 σ ω) q ∧
          22 * (d : ℝ) + ∑ i, τ0 i < ∑ i, (checkerRun C i₀ κ A τ0 σ ω q).τ i} ≤
        ENNReal.ofReal (((n : ℝ) + 2) ^ (-c)) := by sorry

end AdaptiveSparsify
