-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_unitaryXiFrame
-- name    : FiniteEnergyPlane.exists_unitaryXiFrame
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-22T08:59:40.56302+00:00
-- url     : https://prove2.me/theorems/81576cd2-0b77-40bd-a746-7ddd6d889b05
-- title:
--   Unitary frames of $\xi$ along a periodic Reeb orbit exist
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on the contact planes $\xi=\ker\lambda_0\cap TS$, and $P=(x,T)$ a periodic Reeb orbit on $S$. Then $\xi$ admits a **unitary frame along $P$**: a $C^\infty$, $1$-periodic family of linear maps $Z(t):\mathbb{R}^{2n}\to\mathbb{R}^{2n+2}$ such that, for every $t$, $Z(t)$ maps $\mathbb{R}^{2n}$ onto $\xi_{x(Tt)}$, $J(x(Tt))\,Z(t)=Z(t)\,J_0$, and $\omega_0(Z(t)a,Z(t)b)=\langle J_0a,b\rangle$ for all $a,b\in\mathbb{R}^{2n}$ (`IsUnitaryXiFrame`).
--
--   This is the existence half of Hryniewicz, Remark 2.6: $(\xi|_P,J,d\lambda_0)$ pulled back to $\mathbb{R}/\mathbb{Z}$ by $t\mapsto x(Tt)$ is a Hermitian vector bundle of complex rank $n$ over the circle, hence unitarily trivial (since $U(n)$ is connected), and a trivialization can be chosen smooth.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, J. Symplectic Geom. 12 (2014), §2.2.3, Remark 2.6 (existence of a unitary frame of ξ along P); child of FiniteEnergyPlane.asympOp_frame_bridge

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open scoped ContDiff

theorem exists_unitaryXiFrame {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H) :
    ∃ Z : ℝ → CauchyRiemannIndex.Vec n →L[ℝ] V n, IsUnitaryXiFrame J P Z := by sorry

end FiniteEnergyPlane
