-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isAsymptoticEigen_apply_ne_zero_of_unitaryXiFrame
-- name    : FiniteEnergyPlane.isAsymptoticEigen_apply_ne_zero_of_unitaryXiFrame
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-21T15:26:45.629603+00:00
-- url     : https://prove2.me/theorems/258b70ab-d79f-4c30-80a1-bd8847255a2e
-- title:
--   Asymptotic eigenvectors vanish nowhere, given a unitary frame along the orbit
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^4$ be strictly star-shaped, let $J$ be a complex structure on $\xi$, and let $P = (x, T)$ be a periodic Reeb orbit admitting a unitary frame $Z$ of $\xi$ along $P$ (smooth, $1$-periodic, onto $\xi_{x(Tt)}$, $J Z = Z J_0$, $\omega_0(Z a, Z b) = \langle J_0 a, b\rangle$). Let $v$ be an eigenvector of the asymptotic operator $A_P$ with eigenvalue $\mu$: a smooth $1$-periodic $\xi$-loop, not identically zero, with $A_P v = \mu v$. Then $v(t) \neq 0$ for every $t$.
--
--   Role: the same conclusion as `FiniteEnergyPlane.isAsymptoticEigen_apply_ne_zero`, under the existence of a unitary frame along $P$ instead of a global compatibility hypothesis on $J$.
--
--   Formalization Note: no hypothesis on $J$ is made besides those contained in `IsUnitaryXiFrame J P Z`.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6.2 (proof of Lemma 6.9)

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- An eigenvector of the asymptotic operator `A_P` vanishes nowhere, when `J` admits a unitary
frame of `ξ` along `P` (no compatibility hypothesis on `J` away from `P`). -/
theorem isAsymptoticEigen_apply_ne_zero_of_unitaryXiFrame {H : V 1 → ℝ}
    (hH : IsStrictlyStarShapedLevel H) {J : V 1 → V 1 →L[ℝ] V 1} {P : ReebOrbit H}
    {Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1} (hZ : IsUnitaryXiFrame J P Z)
    {μ : ℝ} {v : ℝ → V 1} (hv : IsAsymptoticEigen J P μ v) (t : ℝ) : v t ≠ 0 := by
  sorry

end FiniteEnergyPlane
