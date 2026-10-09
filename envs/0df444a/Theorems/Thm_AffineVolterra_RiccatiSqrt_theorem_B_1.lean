-- Prove2me | Theorems.Thm_AffineVolterra_RiccatiSqrt_theorem_B_1
-- name    : AffineVolterra.RiccatiSqrt.theorem_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:48:17.800781+00:00
-- url     : https://prove2.me/theorems/ebb78351-8579-421f-979a-b45a48f1f9f3
-- title:
--   Theorem B.1, p. 40 — unique non-continuable Volterra solution
-- statement:
--   Let $K$ be a locally square integrable real matrix kernel, $g$ a locally square integrable complex vector function, and $p(t,x)$ a nonlinear drift with $p(\cdot,0)$ locally integrable. Suppose that on each bounded time interval there are $\Theta_T>0$ and a nonnegative $\Pi_T\in L^2(0,T)$ such that
--   $$
--   |p(t,x)-p(t,y)|\le\Pi_T(t)|x-y|+\Theta_T|x-y|(|x|+|y|).
--   $$
--   Then $\psi=g+K*p(\cdot,\psi)$ has a unique non-continuable solution $(\psi,T_{\max})$. If $g$ is real valued and $p$ sends real vectors to real vectors, the solution is real valued almost everywhere before $T_{\max}$. This supplies the maximal solution used by Lemma 6.3.
--
--   **Formalization Note** The time sections $p(\cdot,x)$ are assumed strongly measurable on bounded positive intervals. This necessary condition is implicit in the paper's use of the integral; it does not impose continuity on the $L^1$ forcing. Vector norms are the sup norm, equivalent to the paper's Euclidean norm after a corresponding choice of local constants.
-- source:
--   Abi Jaber, Larsson and Pulido, Affine Volterra processes, arXiv:1708.08796v3, Theorem B.1 and (B.2), p. 40

import Mathlib
import Definitions.Def_AffineVolterra_RiccatiSqrt_Setting

namespace AffineVolterra.RiccatiSqrt

open MeasureTheory

/-- Theorem B.1, p. 40, with measurable dependence on time made explicit. -/
theorem theorem_B_1 {d : ℕ} (K : ℝ → RMat d) (g : ℝ → AffineVolterra.Transform.CVec d)
    (p : ℝ → AffineVolterra.Transform.CVec d → AffineVolterra.Transform.CVec d)
    (hK : RealMatLpLoc 2 K) (hg : VecLpLoc 2 g)
    (hp0 : VecLpLoc 1 (fun t => p t 0))
    (hpmeas : ∀ T : ℝ, 0 < T → ∀ x : AffineVolterra.Transform.CVec d,
      AEStronglyMeasurable (fun t => p t x) (volume.restrict (Set.Ioc 0 T)))
    (hpB2 : ∀ T : ℝ, 0 < T → ∃ (Θ : ℝ) (Pi : ℝ → ℝ),
      0 < Θ ∧ (∀ t ∈ Set.Icc 0 T, 0 ≤ Pi t) ∧
      MemLp Pi 2 (volume.restrict (Set.Ioc 0 T)) ∧
      ∀ t ∈ Set.Icc 0 T, ∀ x y : AffineVolterra.Transform.CVec d,
        ‖p t x - p t y‖ ≤ Pi t * ‖x - y‖ + Θ * ‖x - y‖ * (‖x‖ + ‖y‖)) :
    ∃ (ψ : ℝ → AffineVolterra.Transform.CVec d) (Tmax : ENNReal),
      IsUniqueNonContinuable (fun t => realMatToComplex (K t)) g p ψ Tmax ∧
      ((∀ t : ℝ, 0 ≤ t → ∀ i, (g t i).im = 0) →
        (∀ (t : ℝ) (x : AffineVolterra.Transform.CVec d), 0 ≤ t → (∀ i, (x i).im = 0) →
          ∀ i, (p t x i).im = 0) →
        ∀ T : ℝ, 0 < T → ENNReal.ofReal T < Tmax →
          ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 T)), ∀ i, (ψ t i).im = 0) := by sorry

end AffineVolterra.RiccatiSqrt
