-- Prove2me | Theorems.Thm_AffineVolterra_RiccatiSqrt_corollary_B_3
-- name    : AffineVolterra.RiccatiSqrt.corollary_B_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:48:18.051983+00:00
-- url     : https://prove2.me/theorems/77f9dd46-5a1a-4639-b35a-3f0ed31a93ce
-- title:
--   Corollary B.3, p. 41 — global linear-growth Volterra solution
-- statement:
--   Let $K$ and $G$ be locally square integrable complex matrix functions and $F$ a locally square integrable complex vector function. Suppose $p(t,x)$ is uniformly Lipschitz in $x$, has measurable time sections, and $p(\cdot,0)$ is locally square integrable. The equation
--   $$
--   \chi=F+K*(G\,p(\cdot,\chi))
--   $$
--   has a unique global locally square integrable solution. If $K$ and $F$ are continuous on nonnegative times, this solution has a continuous representative with $\chi(0)=F(0)$. The result supplies the global linear comparison solutions in Lemma 6.3.
--
--   **Formalization Note** Uniform Lipschitz continuity is expressed by one constant for all nonnegative times, as used in (B.4) of the proof. Uniqueness of $L^2$ solutions is almost everywhere.
-- source:
--   Abi Jaber, Larsson and Pulido, Affine Volterra processes, arXiv:1708.08796v3, Corollary B.3, p. 41

import Mathlib
import Definitions.Def_AffineVolterra_RiccatiSqrt_Setting

namespace AffineVolterra.RiccatiSqrt

open MeasureTheory

/-- Corollary B.3, p. 41. -/
theorem corollary_B_3 {d : ℕ} (K : ℝ → CMat d) (F : ℝ → AffineVolterra.Transform.CVec d)
    (G : ℝ → CMat d) (p : ℝ → AffineVolterra.Transform.CVec d → AffineVolterra.Transform.CVec d)
    (hK : ComplexMatLpLoc 2 K) (hF : VecLpLoc 2 F)
    (hG : ComplexMatLpLoc 2 G) (hp0 : VecLpLoc 2 (fun t => p t 0))
    (hpmeas : ∀ T : ℝ, 0 < T → ∀ x : AffineVolterra.Transform.CVec d,
      AEStronglyMeasurable (fun t => p t x) (volume.restrict (Set.Ioc 0 T)))
    (hpLip : ∃ Θ : ℝ, 0 ≤ Θ ∧ ∀ (t : ℝ) (x y : AffineVolterra.Transform.CVec d), 0 ≤ t →
      ‖p t x - p t y‖ ≤ Θ * ‖x - y‖) :
    ∃ χ : ℝ → AffineVolterra.Transform.CVec d,
      IsGlobal K F (fun t x => mulVec (G t) (p t x)) χ ∧
      (∀ φ, IsGlobal K F (fun t x => mulVec (G t) (p t x)) φ →
        ∀ T : ℝ, 0 < T → φ =ᵐ[volume.restrict (Set.Ioc 0 T)] χ) ∧
      ((ContinuousOn K (Set.Ici 0) ∧ ContinuousOn F (Set.Ici 0)) →
        ∃ χc : ℝ → AffineVolterra.Transform.CVec d, ContinuousOn χc (Set.Ici 0) ∧ χc 0 = F 0 ∧
          ∀ T : ℝ, 0 < T → χc =ᵐ[volume.restrict (Set.Ioc 0 T)] χ) := by sorry

end AffineVolterra.RiccatiSqrt
