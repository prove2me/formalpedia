-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isRemovablePuncture_of_abs_aCoord_le
-- name    : FiniteEnergyPlane.isRemovablePuncture_of_abs_aCoord_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-26T17:02:01.799114+00:00
-- url     : https://prove2.me/theorems/43e701be-fd53-4cef-a683-8d51b76fb402
-- title:
--   A puncture with bounded symplectization coordinate is removable
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^{2n+2}$ be a strictly star-shaped level with contact form $\lambda=\lambda_0|_S$ and $d\lambda$-compatible complex structure $J$ on $\xi$, and let $u=(a,w):\dot D=D\setminus\{0\}\to\mathbb R\times S\cong\mathbb R^{2n+2}\setminus\{0\}$ be a finite-energy $\tilde J$-holomorphic curve on the punctured unit disc. If $a\circ u$ is bounded on some punctured neighbourhood $0<|z|<r$ of the puncture, then the puncture is removable: $u$ agrees on $\dot D$ with a smooth $\tilde J$-holomorphic map $D\to\mathbb R^{2n+2}\setminus\{0\}$.
--
--   This is the bounded case of the asymptotic description of finite-energy punctured discs: a puncture that is not removable must send $a$ to $\pm\infty$ along some sequence. No gradient bound or charge condition is assumed.
--
--   **Formalization Note** $\mathbb R\times S$ is identified with $\mathbb R^{2n+2}\setminus\{0\}$ by $(a,x)\mapsto e^{2a}x$, and $a$ is `aCoord H`. Finite energy is Hofer's energy `energy H`, as in `IsFiniteEnergyCurve`. Removability is `IsRemovablePuncture H J u 0 1`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Section 9.2 (the case of a bounded curve near the puncture); H. Hofer, Invent. Math. 114 (1993), Section 3

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A puncture near which the symplectization coordinate `a` stays bounded is removable. -/
theorem isRemovablePuncture_of_abs_aCoord_le {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u)
    (hA : ∃ r : ℝ, 0 < r ∧ ∃ A : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → |aCoord H (u z)| ≤ A) :
    IsRemovablePuncture H J u 0 1 := by
  sorry

end FiniteEnergyPlane
