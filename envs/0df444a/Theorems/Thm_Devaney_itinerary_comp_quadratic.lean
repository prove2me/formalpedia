-- Prove2me | Theorems.Thm_Devaney_itinerary_comp_quadratic
-- name    : Devaney.itinerary_comp_quadratic
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T10:52:19.79434+00:00
-- url     : https://prove2.me/theorems/16c3ff32-5acf-4ecf-801c-6d73065135bf
-- title:
--   Theorem 7.3 — $S \circ F_\mu = \sigma \circ S$
-- statement:
--   For every point $x$ of the invariant set $\Lambda$,
--
--   $$S(F_\mu(x)) = \sigma(S(x)),$$
--
--   that is, applying the quadratic map and then reading off the itinerary is the same as reading off the itinerary and then shifting. Together with Theorem 7.2 this says that $S$ is a topological conjugacy between $F_\mu|_\Lambda$ and the shift.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.7, pp. 46–47, Theorem 7.3

import Mathlib
import Definitions.Def_Devaney_chaos
import Definitions.Def_Devaney_conjugacy
import Definitions.Def_Devaney_sigma2
import Definitions.Def_Devaney_quadratic

namespace Devaney
theorem itinerary_comp_quadratic (μ : ℝ) (x : ℝ) (hx : x ∈ Lambda μ) :
    itinerary μ (quadratic μ x) = shift (itinerary μ x) := by sorry
end Devaney
