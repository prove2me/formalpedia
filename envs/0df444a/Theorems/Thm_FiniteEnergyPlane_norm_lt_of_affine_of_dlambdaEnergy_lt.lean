-- Prove2me | Theorems.Thm_FiniteEnergyPlane_norm_lt_of_affine_of_dlambdaEnergy_lt
-- name    : FiniteEnergyPlane.norm_lt_of_affine_of_dlambdaEnergy_lt
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-22T19:46:59.989151+00:00
-- url     : https://prove2.me/theorems/5f117e57-48d2-48f9-8c9c-19470480c247
-- title:
--   Affinely related planes: the centre stays close when both carry most of the energy on a disc
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n}$ be strictly star-shaped, $u,v:\mathbb{C}\to\mathbb{R}^{2n}$ with $\mathrm{pr}_S\circ u$ differentiable and $v$ nowhere zero, and suppose $u(Az+B)=e^{2c}v(z)$ for all $z$, with $A\neq0$, $B\in\mathbb{C}$, $c\in\mathbb{R}$. If, for some $\rho\in\mathbb{R}$,
--   $$\int_{\mathbb{C}}u^*d\lambda<\int_{\{|z|<\rho\}}u^*d\lambda+\int_{\{|z|<\rho\}}v^*d\lambda ,$$
--   then $|B|<\rho+|A|\rho$.
--
--   When two planes differ by an affine reparametrization and an $\mathbb{R}$-translation, and each carries most of the energy on the same disc, the reparametrization cannot move that disc far away. It is used to keep affine changes between nearby leaves of a family of planes bounded (Hryniewicz 2012, Lemma 7.2).
--
--   **Formalization Note** $e^{2c}v$ is the $\mathbb{R}$-translation `shiftA c v` written out; the energies are `dlambdaEnergy` (values in $[0,\infty]$).
-- source:
--   General lemma; used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Lemma 7.2

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `u, v : ℂ → V n` with `proj H ∘ u` differentiable, `v` nonvanishing, and
`u (A z + B) = e^{2c} v z` for all `z`, where `A ≠ 0`. If the `dλ`-energies of `u` and of `v` on
`ball 0 ρ` add up to more than the total `dλ`-energy of `u`, then `‖B‖ < ρ + ‖A‖ ρ`. -/
theorem norm_lt_of_affine_of_dlambdaEnergy_lt {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (u v : ℂ → V n) (c : ℝ) (A B : ℂ) (hA : A ≠ 0)
    (hw : Differentiable ℝ (fun y => proj H (u y))) (hv0 : ∀ z, v z ≠ 0)
    (hrel : ∀ z, u (A * z + B) = Real.exp (2 * c) • v z) (ρ : ℝ)
    (hlt : dlambdaEnergy H Set.univ u <
      dlambdaEnergy H (ball 0 ρ) u + dlambdaEnergy H (ball 0 ρ) v) :
    ‖B‖ < ρ + ‖A‖ * ρ := by
  sorry

end FiniteEnergyPlane
