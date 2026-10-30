-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_canonical_transverse_coordinates_of_variation
-- name    : BirkhoffGlobalSection.canonical_transverse_coordinates_of_variation
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-29T19:40:46.79469+00:00
-- url     : https://prove2.me/theorems/b4312b3d-4c65-45ab-b5f0-9bfa373f5a68
-- title:
--   Canonical transverse coordinates of a Hamiltonian variation
-- statement:
--   Let $x$ be a periodic Hamiltonian orbit in the strictly convex star-shaped region of $G$, and let $Y$ be its variational flow with $Y(0)=I$. Assume the canonical radial frames $F(t)$ are symplectic. For an initial tangent vector $v$, write $z_0$ for the last two coordinates of $F(0)^{-1}\mathrm{toHryn}(v)$, and let $\phi$ be the canonical transverse path. Then $Y(\tau T)v$ remains tangent, and
--
--   $$\bigl(F(\tau T)^{-1}\mathrm{toHryn}(Y(\tau T)v)\bigr)_{2,3}=\phi(\tau)z_0.$$
--
--   Thus the canonical transverse block represents every tangent variation after quotienting out the Hamiltonian direction. The statement applies to arbitrary real parameter $\tau$.
-- source:
--   Derived flow-coordinate lemma for BirkhoffGlobalSection.radial_contact_transverse_angle_conjugacy, https://prove2.me/theorems/eab3aa7c-2cfb-4515-b659-4ccc36142c64. Uses its exact canonical radial frame and variational equation. Generic symplectic pairing/reconstruction adapted with credit to Mazecto accepted submission 893234ef-5ec2-4f4b-b415-f79ec1030002; local C2 transport is supplied by HryniewiczCriterion.local_C2_variational_transport.

import Mathlib
import Definitions.Def_BirkhoffGlobalSection_CanonicalPositiveFrame
import Definitions.Def_BirkhoffGlobalSection_RegularizationModel
open BirkhoffGlobalSection HryniewiczCriterion

theorem BirkhoffGlobalSection.canonical_transverse_coordinates_of_variation
    (G : Phase → ℝ) (x : ℝ → Phase) (T : ℝ)
    (hx : IsPeriodicHamiltonianSolutionIn G {y | IsStrictlyConvexStarShapedAt G y} x T)
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY0 : Y 0 = ContinuousLinearMap.id ℝ Phase)
    (hY : ∀ t : ℝ, HasDerivAt Y
      ((fderiv ℝ (BirkhoffGlobalSection.hamiltonianVectorField G) (x t)).comp (Y t)) t)
    (v : Phase) (hv : fderiv ℝ G (x 0) v = 0)
    (hsp : ∀ t, (canonicalRadialFrame G x t).transpose * omegaMat *
      canonicalRadialFrame G x t = omegaMat) (τ : ℝ) :
    fderiv ℝ G (x (τ * T)) (Y (τ * T) v) = 0 ∧
    (fun i : Fin 2 => ((canonicalRadialFrame G x (τ * T))⁻¹.mulVec
      (toHryn (Y (τ * T) v))) i.succ.succ) =
    (canonicalTransversePath G x T Y τ).mulVec
      (fun i : Fin 2 => ((canonicalRadialFrame G x 0)⁻¹.mulVec (toHryn v)) i.succ.succ) := by sorry
