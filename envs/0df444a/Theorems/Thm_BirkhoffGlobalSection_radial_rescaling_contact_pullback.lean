-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_radial_rescaling_contact_pullback
-- name    : BirkhoffGlobalSection.radial_rescaling_contact_pullback
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-30T17:02:01.255494+00:00
-- url     : https://prove2.me/theorems/37bf7bc6-4d14-48b7-9e50-6610d9d83f52
-- title:
--   Radial rescaling pulls back the radial contact primitive by the squared scale
-- statement:
--   Let alpha be the coordinate radial primitive compatible with the Hamiltonian convention X_H=(H_p,-H_q). For any real scalar function a on four-dimensional phase space differentiable at y, put R(x)=a(x)x. For every vector v,
--
--   $$\alpha_{a(y)y}(DR_y v)=a(y)^2\alpha_y(v).$$
--
--   The derivative of the scale contributes only a radial vector, which the primitive annihilates. This ambient identity does not require a to be positive or nonzero; wherever it is nonzero the squared factor preserves contact coorientation. It supplies the contact-form calculation for radial normalization of star-shaped Hamiltonian levels. Radial invertibility, Reeb-flow compatibility and global-section existence are separate results.
-- source:
--   Auxiliary ambient generalization of the star-shaped sphere pullback formula in Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, arXiv:1105.2077v5, p. 2, https://arxiv.org/pdf/1105.2077. Derived by the product derivative and alternation of the radial primitive, translated to the workspace Hamiltonian sign convention; not a verbatim source theorem.

import Definitions.Def_BirkhoffGlobalSection_TransverseHopf
import Mathlib.Analysis.Calculus.FDeriv.Mul
open BirkhoffGlobalSection

theorem BirkhoffGlobalSection.radial_rescaling_contact_pullback (a : Phase → ℝ) (y v : Phase)
    (ha : DifferentiableAt ℝ a y) :
    phaseRadialContact (a y • y)
      (fderiv ℝ (fun x : Phase => a x • x) y v) =
        (a y) ^ 2 * phaseRadialContact y v := by sorry
