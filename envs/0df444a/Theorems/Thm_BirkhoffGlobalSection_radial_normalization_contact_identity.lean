-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_radial_normalization_contact_identity
-- name    : BirkhoffGlobalSection.radial_normalization_contact_identity
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-27T04:38:28.137418+00:00
-- url     : https://prove2.me/theorems/88f0db9c-eeaf-496d-9e10-8978b0c2d934
-- title:
--   Radial normalization scales the radial contact form by the inverse squared radius
-- statement:
--   For a nonzero point $y\in\mathbb R^4$, put $N(y)=\sum_i y_i^2$ and $r(y)=y/\sqrt{N(y)}$. The radial map is smooth near $y$, has values in the unit three-sphere, is odd, and satisfies
--
--   $$\alpha_{r(y)}(Dr_yv)=\frac{\alpha_y(v)}{N(y)}\qquad(v\in\mathbb R^4),$$
--
--   where $\alpha_y(v)=-\omega(y,v)/2$. In particular, radial normalization preserves positivity of contact evaluation. The identity applies to all ambient vectors and uses Euclidean squared radius independently of the norm instance on the coordinate space.
-- source:
--   Direct identity from Def_BirkhoffGlobalSection_TransverseHopf: r(y)=N(y)^(-1/2)y and alpha_y(v)=-omega(y,v)/2. Bilinearity and omega(y,y)=0 give r^*alpha=N^(-1)alpha. These are the homogeneous radial contact-form conventions used in Hryniewicz–Salomão, arXiv:1505.02713v3, Section 1.3, https://arxiv.org/html/1505.02713v3.

import Definitions.Def_BirkhoffGlobalSection_TransverseHopf
open scoped ContDiff

namespace BirkhoffGlobalSection

theorem radial_normalization_contact_identity
    (y : Phase) (hy : 0 < zNormSq y + wNormSq y) :
    ContDiffAt ℝ ∞ radialNormalize y ∧
      radialNormalize y ∈ unitThreeSphere ∧
      radialNormalize (-y) = -radialNormalize y ∧
      ∀ v : Phase,
        phaseRadialContact (radialNormalize y) (fderiv ℝ radialNormalize y v) =
          phaseRadialContact y v / (zNormSq y + wNormSq y) := by sorry

end BirkhoffGlobalSection
