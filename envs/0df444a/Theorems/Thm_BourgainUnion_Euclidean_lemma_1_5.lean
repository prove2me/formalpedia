-- Prove2me | Theorems.Thm_BourgainUnion_Euclidean_lemma_1_5
-- name    : BourgainUnion.Euclidean.lemma_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:26:33.379991+00:00
-- url     : https://prove2.me/theorems/855d25cc-deb1-4241-853e-7ee335cd3327
-- title:
--   Lemma 1.5 — extension bounds for both Euclidean classes
-- statement:
--   Let a finite metric space $X$ be covered by $k\ge1$ subsets $U_i$, and write $e_{\max}$ for their maximal ambient Lipschitz extension constant after dropping empty members. The source's two bounds are made explicit using its optimized exponents:
--   $$\begin{aligned}
--   \text{all }U_i\text{ Euclidean}:&&e_{\max}&\le k^{\eta_0}\le k^{141/125},\\
--   \text{all }U_i\text{ one-point strongly Euclidean}:&&e_{\max}&\le e^{\eta_1}k^{\eta_1}\le e^{\eta_1}k^{179/200}.
--   \end{aligned}$$
--   The statement also certifies the defining root equation for $\eta_0$, the minimizing property for $\eta_1$, and the proof's intervals
--   $$1<\eta_0<141/125,\qquad 8941/10000<\eta_1<89417/100000<179/200.$$
--   The gap polynomial $D_{\eta_1}$ is nonnegative on $[0,1]$. These certificates rule out real-infimum default values. The factors are universal and independent of $X$, the cover and the map being extended. Both branches of the printed lemma remain present.
--
--   Differences from the source:
--   - encoding: real ℓ₂ and finite or infinite Euclidean target spaces → square-summable real sequences H2, with equivalent separable real Hilbert spaces where a dimension varies; reason: lp (fun _ : ℕ => ℝ) 2 is real ℓ₂; each separable real Hilbert space is isometric to a finite- or countably-dimensional ℓ₂ space
--   - encoding: a finite indexed cover that may overlap → U : Fin k → Set X and pointwise coverage; reason: zero-based indexing only; overlap and empty members are permitted unless nonemptiness is stated
--   - encoding: the least distortion or extension factor, potentially infinite → an infimum in ℝ≥0∞ of finite admissible factors at least one; reason: empty admissible sets give infinity; no real infimum default or unjustified attainment is used; empty and singleton spaces have the conventional factor one
--   - generalization: O(k^1.128) and O(k^0.895) → k^η₀ and exp(η₁)k^η₁, together with the stated decimal-exponent bounds and the defining certificates; reason: equations (16), (18), (19) and pp. 20–23 supply these exact constants; 141/125 and 179/200 equal the printed exponents; the explicit form implies the source's asymptotic statement
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 3, Lemma 1.5; proof §§4.6–4.9, pp. 20–23

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_ExtensionModel
import Definitions.Def_BourgainUnion_Euclidean_Exponents

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean

/-- Lemma 1.5 with the proof's exact exponents and rational certificates, pp.20--23. -/
theorem lemma_1_5 :
    1 < eta0 ∧ eta0 < (141/125 : ℝ) ∧
    eta0*(eta0+2)*(eta0^2+4*eta0-4) = 2*Real.pi ∧
    (8941/10000 : ℝ) < eta1 ∧ eta1 < (89417/100000 : ℝ) ∧
    (∀ z ∈ Set.Icc (0:ℝ) 1, 0 ≤ exponentGap eta1 z) ∧
    (∀ η : ℝ, 0 ≤ η → (∀ z ∈ Set.Icc (0:ℝ) 1, 0 ≤ exponentGap η z) → eta1 ≤ η) ∧
    (∀ (X : Type) [MetricSpace X] [Fintype X] (k : ℕ), 1 ≤ k →
      ∀ U : Fin k → Set X, Covers U →
      ((∀ i, IsEuclidean (U i)) →
        eMax U ≤ ENNReal.ofReal ((k:ℝ)^eta0) ∧
        eMax U ≤ ENNReal.ofReal ((k:ℝ)^(141/125:ℝ))) ∧
      ((∀ i, OneStrong (U i)) →
        eMax U ≤ ENNReal.ofReal (Real.exp eta1 * (k:ℝ)^eta1) ∧
        eMax U ≤ ENNReal.ofReal (Real.exp eta1 * (k:ℝ)^(179/200:ℝ)))) := by sorry

end BourgainUnion.Euclidean
