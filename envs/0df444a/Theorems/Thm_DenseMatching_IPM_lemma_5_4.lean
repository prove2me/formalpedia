-- Prove2me | Theorems.Thm_DenseMatching_IPM_lemma_5_4
-- name    : DenseMatching.IPM.lemma_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:38:58.348661+00:00
-- url     : https://prove2.me/theorems/adfd8276-ebb5-4623-ac42-5b35efd916a0
-- title:
--   Lemma 5.4 — E Tr[(Σ_i ζ_i u_i u_i⊤)⁶] ≤ 10² a³ n for independent centered ζ_i ≥ −1
-- statement:
--   Let $I$ be a finite index set, $u_i\in\mathbb R^n$, and let $\zeta_i$, $i\in I$, be independent real random variables with $\mathbb E[\zeta_i]=0$ and $\zeta_i\ge-1$ almost surely; put $Q_i=\zeta_iu_iu_i^\top$. Suppose $\sum_iu_iu_i^\top\preceq I$ and, for some $a\in[0,1]$,
--   $$\mathbb E[|\zeta_i|^p]\,\|u_i\|^{2p-2}\le a^{p-1}\quad\text{for every } i \text{ and } p=2,\dots,6 .$$
--   Then
--   $$\mathbb E\Big[\mathrm{Tr}\Big[\Big(\sum_iQ_i\Big)^6\Big]\Big]\le10^2a^3n.$$
--   It is the sixth-moment estimate behind the resistance estimator of §5.
--
--   Differences from the source:
--   - reading: 'Q_i … be independent' → the ζ_i are mutually independent (iIndepFun); reason: the u_i are deterministic, so the Q_i are independent exactly when the ζ_i with u_i ≠ 0 are; the paper's hypotheses are on the ζ_i
--   - reading: 'for some a ≤ 1' → 0 ≤ a ≤ 1; reason: a ≥ E[ζ_i²]‖u_i‖² ≥ 0 whenever I is nonempty; for I = ∅ and a < 0 the printed bound would read 0 ≤ 10²a³n < 0
--   - encoding: E[|ζ_i|^p] ‖u_i‖^{2p−2} and E[ζ_i] = 0 → (∫⁻ ‖ζ_i‖ₑ^p) · (Σ_j u_ij²)^{p−1} in [0, ∞] (with ∞ · 0 = 0), and Integrable ζ_i with ∫ ζ_i = 0; reason: ‖·‖ is the Euclidean norm; E[ζ_i] = 0 presupposes the mean exists
--   - encoding: E[Tr[(Σ_i Q_i)^6]] → lintegral of ENNReal.ofReal of the trace; reason: the trace of an even power of a symmetric matrix is ≥ 0, so this is the expectation, with no integrability side condition
-- source:
--   Dai, Peng, Sleator, Stepin, Yang, Approaching Optimality for Dense Bipartite Matching, STOC 2027 submission (manuscript sha256 0bdeb447…), p. 59, Lemma 5.4

import Mathlib

open MeasureTheory ProbabilityTheory Matrix

namespace DenseMatching.IPM

/-- Lemma 5.4 (p. 59). Let `Q_i = ζ_i u_i u_i⊤`, `i ∈ I` (finite), with `u_i ∈ ℝⁿ` and independent
real random variables `ζ_i` with `E[ζ_i] = 0` and `ζ_i ≥ −1` almost surely, such that
`∑_i u_i u_i⊤ ⪯ I` and, for some `a ∈ [0, 1]`, `E[|ζ_i|^p] ‖u_i‖^{2p−2} ≤ a^{p−1}` for every `i` and
`p = 2, …, 6`. Then `E[Tr[(∑_i Q_i)⁶]] ≤ 10² a³ n`. -/
theorem lemma_5_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) {I : Type*} [Fintype I] (ζ : I → Ω → ℝ) (u : I → Fin n → ℝ) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hind : iIndepFun ζ P) (hint : ∀ i, Integrable (ζ i) P)
    (hmean : ∀ i, ∫ ω, ζ i ω ∂P = 0) (hlow : ∀ i, ∀ᵐ ω ∂P, -1 ≤ ζ i ω)
    (hsum : (1 - ∑ i, vecMulVec (u i) (u i)).PosSemidef)
    (hmom : ∀ i, ∀ p ∈ Finset.Icc 2 6,
      (∫⁻ ω, ‖ζ i ω‖ₑ ^ p ∂P) * ENNReal.ofReal ((∑ j, u i j ^ 2) ^ (p - 1)) ≤
        ENNReal.ofReal (a ^ (p - 1))) :
    ∫⁻ ω, ENNReal.ofReal (Matrix.trace ((∑ i, ζ i ω • vecMulVec (u i) (u i)) ^ 6)) ∂P ≤
      ENNReal.ofReal (10 ^ 2 * a ^ 3 * n) := by sorry

end DenseMatching.IPM
