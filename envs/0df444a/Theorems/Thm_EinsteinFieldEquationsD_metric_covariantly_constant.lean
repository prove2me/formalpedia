-- Prove2me | Theorems.Thm_EinsteinFieldEquationsD_metric_covariantly_constant
-- name    : EinsteinFieldEquationsD.metric_covariantly_constant
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:11:59.826232+00:00
-- url     : https://prove2.me/theorems/cc19a183-cf08-4c7f-bddc-008dc4ef531f
-- title:
--   The metric is covariantly constant
-- statement:
--   Let $g$ be a smooth, symmetric, nondegenerate metric on an open set $U\subseteq\mathbb{R}^D$. Then $g$ is covariantly constant for its Levi-Civita connection:
--   $$\nabla_\lambda g_{\mu\nu}=\partial_\lambda g_{\mu\nu}-\Gamma^\sigma_{\lambda\mu}g_{\sigma\nu}-\Gamma^\sigma_{\lambda\nu}g_{\mu\sigma}=0\quad\text{on }U.$$
-- source:
--   Wikipedia, "Einstein field equations", revision oldid=1374672993, https://en.wikipedia.org/w/index.php?title=Einstein_field_equations&oldid=1374672993; section 'Features — Conservation of energy and momentum', derivation box

import Mathlib
import Definitions.Def_EinsteinFieldEquationsD_Defs

namespace EinsteinFieldEquationsD

theorem metric_covariantly_constant {D : ℕ} (g : Tensor2 D) (U : Set (Coord D)) (hg : IsMetricOn g U) :
    ∀ x ∈ U, ∀ l a b : Fin D, covDeriv2 g g x l a b = 0 := by sorry

end EinsteinFieldEquationsD
