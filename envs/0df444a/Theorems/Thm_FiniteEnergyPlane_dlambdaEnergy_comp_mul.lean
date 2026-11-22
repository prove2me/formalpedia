-- Prove2me | Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_comp_mul
-- name    : FiniteEnergyPlane.dlambdaEnergy_comp_mul
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-21T11:04:38.417122+00:00
-- url     : https://prove2.me/theorems/efa2e531-4052-42a8-b2ee-1faef6df7270
-- title:
--   The dλ-energy under a complex-linear change of variables
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be as in `FiniteEnergyPlane_Setting`, with radial projection $\mathrm{proj}$ onto $S$. Let $u:\mathbb{C}\to\mathbb{R}^{2n+2}$ be such that $w=\mathrm{proj}\circ u$ is (real) differentiable, and let $A\in\mathbb{C}\setminus\{0\}$. Then for every measurable set $s\subset\mathbb{C}$,
--   $$\int_s (u\circ m_A)^*d\lambda \;=\; \int_{A\cdot s} u^*d\lambda ,\qquad m_A(z)=Az,$$
--   where both sides are the $d\lambda$-energies `dlambdaEnergy` (Lebesgue integrals of the positive part of the density $\omega_0(\partial_s w,\partial_t w)$).
--
--   Role: the $d\lambda$-energy of a curve is unchanged by complex-linear reparametrizations of the domain (rotations and dilations), with the domain set transported accordingly. This is used to compare normalization conditions such as $\int_{\{|z|>1\}}u^*d\lambda=\gamma$ for two planes that differ by such a reparametrization.
--
--   **Formalization Note** The density is `dlambdaDensity`, built from `ds`, `dt` (the real derivatives in the directions $1$ and $i$); only differentiability of $\mathrm{proj}\circ u$ is assumed, no holomorphicity.
-- source:
--   Change of variables for the dλ-energy of finite-energy curves; used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 7.1

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `A ∈ ℂ` be nonzero and let `u : ℂ → V n` be such that `proj H ∘ u` is differentiable. For
every measurable `s ⊆ ℂ`, the `dλ`-energy of `z ↦ u (A z)` on `s` equals the `dλ`-energy of `u` on
the image `A · s`. -/
theorem dlambdaEnergy_comp_mul {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) (A : ℂ) (hA : A ≠ 0)
    (hw : Differentiable ℝ (fun y => proj H (u y))) (s : Set ℂ) (hs : MeasurableSet s) :
    dlambdaEnergy H s (fun z => u (A * z)) = dlambdaEnergy H ((fun y => A * y) '' s) u := by
  sorry

end FiniteEnergyPlane
