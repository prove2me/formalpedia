-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_positive_time_change_bundle
-- name    : BirkhoffGlobalSection.positive_time_change_bundle
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-02T12:48:23.71806+00:00
-- url     : https://prove2.me/theorems/186fbb34-0e3f-481f-97c6-c071c9fdb1bd
-- title:
--   Positive time change of variational solutions and transverse angular bounds
-- statement:
--   Let $X$ be a differentiable vector field, $b>0$ a differentiable rate along a supplied trajectory $x'=X(x)$, and let a differentiable clock reparametrize it with inverse-clock derivative $\tau'=b(x\circ\tau)$. Supplied variational vectors and matrices are related by explicitly defined corrections in the flow direction. With the continuity assumptions stated in the formal result, the corrected paths satisfy the appropriate linearized equations for $X$ and $bX$ and have the prescribed initial values.
--
--   For a Hamiltonian field $X_H$, quaternionic transverse coordinates ignore the flow-direction correction:
--   $$C_y(v+cX_H(y))=C_y(v).$$
--   Under an order clock with matching endpoints, every supplied continuous polar angle retains its endpoint increment. Consequently an assumed universal Hamiltonian transverse angular bound above $2\pi$ transfers to every normalized variational matrix initialized at the identity. This does not define or identify a Conley--Zehnder index.
--
--   **Formalization Note.** This theorem is the conjunction of 7 individually quantified results. Each conjunct retains the exact hypotheses of its local proof; the inventory is recorded with the publication artifacts.
-- source:
--   Original auxiliary results supporting the Birkhoff global-section formalization. Reeb and radial conventions: Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, arXiv:1105.2077v5, equations (1)-(2), Section 2.1.1 and the radial model on p. 2, https://arxiv.org/pdf/1105.2077 . Quaternionic conventions: Joung--van Koert, arXiv:2407.19159v3, Section 2.3. Supporting calculus and arithmetic: Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474, https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib. The auxiliary identities are original coordinate and calculus arguments; this is not a claimed formalization of the analytic prescribed-binding theorem. Local outcome documentation: notes/POSITIVE_TIME_CHANGE_WINDING.md.

import Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Module
import Definitions.Def_BirkhoffGlobalSection_ContactVariationalInterfaces
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false

theorem BirkhoffGlobalSection.positive_time_change_bundle :
(∀ (F : Phase → ℝ) (y w : Phase) (c : ℝ),
    transverseFrameCoordinates (TangentialHessian.grad F y)
      (w + c • hamiltonianVectorField F y) =
        transverseFrameCoordinates (TangentialHessian.grad F y) w) ∧
(∀ (r k l : ℝ → ℝ) (hr : Continuous r) (hk : Continuous k)
    (hpos : ∀ t, 0 < r t) (hdr : ∀ t, HasDerivAt r (r t * l t) t),
    let η : ℝ → ℝ := fun t => r t * ∫ s in (0 : ℝ)..t, k s / r s
    η 0 = 0 ∧ ∀ t, HasDerivAt η (k t + η t * l t) t) ∧
(∀ {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (X : E → E) (b : E → ℝ) (x u : ℝ → E) (τ : ℝ → ℝ)
    (hx : ∀ s, HasDerivAt x (X (x s)) s)
    (hu : ∀ s, HasDerivAt u (fderiv ℝ X (x s) (u s)) s)
    (hτ : ∀ t, HasDerivAt τ (b (x (τ t))) t)
    (hX : ∀ t, DifferentiableAt ℝ X (x (τ t)))
    (hb : ∀ t, DifferentiableAt ℝ b (x (τ t)))
    (hpos : ∀ t, 0 < b (x (τ t)))
    (hk : Continuous (fun t => fderiv ℝ b (x (τ t)) (u (τ t)))),
    let η : ℝ → ℝ := fun t => b (x (τ t)) *
      ∫ s in (0 : ℝ)..t, fderiv ℝ b (x (τ s)) (u (τ s)) / b (x (τ s))
    let z : ℝ → E := fun t => u (τ t) + η t • X (x (τ t))
    η 0 = 0 ∧ z 0 = u (τ 0) ∧
      ∀ t, HasDerivAt z (fderiv ℝ (fun y => b y • X y) (x (τ t)) (z t)) t) ∧
(∀ (F : Phase → ℝ) (b : Phase → ℝ) (x : ℝ → Phase)
    (Y : ℝ → (Phase →L[ℝ] Phase)) (τ : ℝ → ℝ)
    (hx : ∀ s, HasDerivAt x (hamiltonianVectorField F (x s)) s)
    (hY : ∀ s, HasDerivAt Y
      ((fderiv ℝ (hamiltonianVectorField F) (x s)).comp (Y s)) s)
    (hY0 : Y 0 = ContinuousLinearMap.id ℝ Phase) (hτ0 : τ 0 = 0)
    (hτ : ∀ t, HasDerivAt τ (b (x (τ t))) t)
    (hX : ∀ t, DifferentiableAt ℝ (hamiltonianVectorField F) (x (τ t)))
    (hb : ∀ t, DifferentiableAt ℝ b (x (τ t)))
    (hpos : ∀ t, 0 < b (x (τ t)))
    (hk : ∀ v : Phase, Continuous (fun t => fderiv ℝ b (x (τ t)) (Y (τ t) v))),
    ∀ v : Phase, ∃ z : ℝ → Phase,
      z 0 = v ∧
      (∀ t, HasDerivAt z
        (fderiv ℝ (fun y => b y • hamiltonianVectorField F y) (x (τ t)) (z t)) t) ∧
      (∀ t, transverseFrameCoordinates (TangentialHessian.grad F (x (τ t))) (z t) =
        transverseFrameCoordinates (TangentialHessian.grad F (x (τ t))) (Y (τ t) v))) ∧
(∀ (p q : ℝ → Plane) (τ : ℝ ≃o ℝ)
    (T S B : ℝ) (hτ0 : τ 0 = 0) (hτS : τ S = T)
    (heq : ∀ t, q t = p (τ t))
    (hbound : ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧ p t = ![r * Real.cos (θ t), r * Real.sin (θ t)]) →
      B < θ T - θ 0),
    ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧ q t = ![r * Real.cos (θ t), r * Real.sin (θ t)]) →
      B < θ S - θ 0) ∧
(∀ {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (X : E → E) (b : E → ℝ) (x : ℝ → E) (C : ℝ ≃o ℝ)
    (Z : ℝ → (E →L[ℝ] E))
    (hx : ∀ t, HasDerivAt x (X (x t)) t)
    (hC : ∀ t, HasDerivAt C (b (x t))⁻¹ t)
    (hZ : ∀ t, HasDerivAt Z
      ((fderiv ℝ (fun y => b y • X y) (x (C.symm t))).comp (Z t)) t)
    (hX : ∀ t, DifferentiableAt ℝ X (x t))
    (hb : ∀ t, DifferentiableAt ℝ b (x t))
    (hne : ∀ t, b (x t) ≠ 0)
    (hk : Continuous (fun t => (b (x t))⁻¹ •
      ((fderiv ℝ b (x t)).comp (Z (C t))))),
    let η : ℝ → (E →L[ℝ] ℝ) := fun t =>
      -(∫ s in (0 : ℝ)..t, (b (x s))⁻¹ • ((fderiv ℝ b (x s)).comp (Z (C s))))
    let Y : ℝ → (E →L[ℝ] E) := fun t => Z (C t) + (η t).smulRight (X (x t))
    Y 0 = Z (C 0) ∧
      ∀ t, HasDerivAt Y ((fderiv ℝ X (x t)).comp (Y t)) t) ∧
(∀ (F : Phase → ℝ) (b : Phase → ℝ) (x : ℝ → Phase) (C : ℝ ≃o ℝ)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (T S : ℝ)
    (hwind : HasTransverseWindingAboveOne F x T)
    (hx : ∀ t, HasDerivAt x (hamiltonianVectorField F (x t)) t)
    (hC0 : C 0 = 0) (hCT : C T = S)
    (hC : ∀ t, HasDerivAt C (b (x t))⁻¹ t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase)
    (hZ : ∀ t, HasDerivAt Z
      ((fderiv ℝ (fun y => b y • hamiltonianVectorField F y) (x (C.symm t))).comp (Z t)) t)
    (hX : ∀ t, DifferentiableAt ℝ (hamiltonianVectorField F) (x t))
    (hb : ∀ t, DifferentiableAt ℝ b (x t))
    (hpos : ∀ t, 0 < b (x t))
    (hk : Continuous (fun t => (b (x t))⁻¹ •
      ((fderiv ℝ b (x t)).comp (Z (C t)))))
    (v : Phase) (hv : fderiv ℝ F (x 0) v = 0)
    (hvn : transverseFrameCoordinates (TangentialHessian.grad F (x 0)) v ≠ 0),
    ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧
        transverseFrameCoordinates (TangentialHessian.grad F (x (C.symm t))) (Z t v) =
          ![r * Real.cos (θ t), r * Real.sin (θ t)]) →
      2 * Real.pi < θ S - θ 0) := by sorry
