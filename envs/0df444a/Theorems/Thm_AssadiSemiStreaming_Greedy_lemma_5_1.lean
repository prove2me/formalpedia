-- Prove2me | Theorems.Thm_AssadiSemiStreaming_Greedy_lemma_5_1
-- name    : AssadiSemiStreaming.Greedy.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:39:32.240173+00:00
-- url     : https://prove2.me/theorems/341e8e27-5223-4d3d-a670-4adab2aec816
-- title:
--   Lemma 5.1 — Normalization, symmetric maxima and exact zero-absorption probability
-- statement:
--   Lemma 5.1. Consider the assignment µ : {1, . . . , 2m − 1} → [0, 1] such that for i ∈ [m],
--   µ(i) := γ_m · (2 · (2m + 1))/((2m − i) · (2m − i + 1) · (2m − i + 2)) for γ_m := (2m · (m + 1))/(3m + 1),
--   and for i ∈ [m + 1 : 2m − 1], µ(i) = 0.
--   Firstly, µ is a distribution. Secondly, if we sample a random walk W starting from a state distributed according to µ—denoting the combined distribution by D_m—, then, for all j ∈ [2m − 1],
--   Pr_{W∼D_m}(W ends in 0 ∧ w_max(W) = j) = Pr_{W∼D_m}(W ends in 0 ∧ w_max(W) = 2m − j).
--   Finally,
--   Pr_{W∼D_m}(W ends in 0) = 2m/(3m + 1).
--
--   All three conclusions are included for every m≥1: nonnegative unit-sum weights, symmetry of the joint zero-absorption-and-maximum event, and the exact zero-absorption probability. No normalization or symmetry is assumed.
--
--   Differences from the source:
--   - encoding: real-valued weights given by rational formulas → rational weights cast to real numbers where probabilities are used; reason: all source weights are rational and the casts preserve the formulas exactly
--   - encoding: probabilities of the infinite-time joint event → nonnegative extended-real sums of disjoint first-absorption events; reason: all finite absorption times are included and divergence cannot acquire a zero default
--   - encoding: μ is defined on interior states → μ is extended by zero to all natural states; reason: the extension changes no weight or probability on the source domain
-- source:
--   Assadi, Jiang and Xiang (2026), Semi-Streaming Matching in a Single Pass II: Greedy is Optimal, supplied STOC 2027 submission manuscript (published basis per source.meta.json; SHA-256 8f66fdf7cb422cdd3accbae4cb24ebc61dd7ddb2e5e2d5422f4de6fc3f99395d), Lemma 5.1, printed p. 13 / PDF 15

import Definitions.Def_AssadiSemiStreaming_Greedy_WalkLaws

namespace AssadiSemiStreaming.Greedy

theorem lemma_5_1 (m : ℕ) (hm : 1 ≤ m) :
    (∀ i : ℕ, 0 ≤ mu m i ∧ mu m i ≤ 1) ∧
    (∑ i ∈ Finset.Icc 1 (2 * m - 1), mu m i) = 1 ∧
    (∀ j : ℕ, 1 ≤ j → j < 2 * m → mixtureMaxProb m j = mixtureMaxProb m (2 * m - j)) ∧
    mixtureZeroProb m = (2 * m : ℝ) / (3 * m + 1) := by sorry

end AssadiSemiStreaming.Greedy
