-- Prove2me | Theorems.Thm_FiniteEnergyPlane_memLp_four_of_exp_bound
-- name    : FiniteEnergyPlane.memLp_four_of_exp_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-09T22:32:27.621267+00:00
-- url     : https://prove2.me/theorems/5967f8fd-02c4-4842-a4a2-eb93d135ac89
-- title:
--   Exponential decay in s gives L^4 on the cylinder
-- statement:
--   Let $E$ be a normed group, $\kappa > 0$, $C \in \mathbb{R}$, and $f : \mathbb{R}\times\mathbb{R} \to E$ almost everywhere strongly measurable for Lebesgue measure on the strip $\mathbb{R}\times[0,1)$ (`cylMeasure`). If $\|f(s,t)\| \le C e^{-\kappa|s|}$ for all $s, t$, then $f \in L^4(\mathbb{R}\times[0,1))$.
--
--   **Role.** A convenient membership test for $L^4$ on the cylinder $\mathbb{R}\times S^1$, used for coefficients and weights that decay exponentially at both ends.
-- source:
--   Setting of C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry (arXiv:1011.1690), Ch. 4

import Definitions.Def_CauchyRiemannIndex_Setting

namespace FiniteEnergyPlane

open MeasureTheory CauchyRiemannIndex

/-- A strongly measurable `f` on the strip with `‖f (s, t)‖ ≤ C e^{-κ|s|}`, `κ > 0`, lies in
`L⁴(cylMeasure)`. -/
theorem memLp_four_of_exp_bound {E : Type*} [NormedAddCommGroup E] (f : ℝ × ℝ → E)
    (hf : AEStronglyMeasurable f cylMeasure) (C κ : ℝ) (hκ : 0 < κ)
    (hb : ∀ s t, ‖f (s, t)‖ ≤ C * Real.exp (-(κ * |s|))) : MemLp f 4 cylMeasure := by
  sorry

end FiniteEnergyPlane
