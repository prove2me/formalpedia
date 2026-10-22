-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_antipodal_double_cover_descends_to_prime_binding
-- name    : BirkhoffGlobalSection.antipodal_double_cover_descends_to_prime_binding
-- status  : Proved
-- author  : @Yivy Yu
-- created : 2026-09-12T15:09:41.876908+00:00
-- url     : https://prove2.me/theorems/7980ece4-f5a9-4fa6-8a6a-a57ab2e85249
-- title:
--   A double lift descends to a prime quotient binding
-- statement:
--   Let the selected Levi-Civita component carry a free, component-preserving antipodal deck map, and let its flow commute with that map. If a lifted periodic orbit has least positive period $T$ and reaches its antipodal point at time $T/2$, then its image in the antipodal quotient is a prime periodic orbit of period $T/2$.
--
--   This is the formal lift-to-quotient bridge for the binding: no quotient return can occur at a time strictly between $0$ and $T/2$. A return to the same lift would contradict minimality of $T$; a return to the antipodal lift would produce a lifted return at twice that time.
-- source:
--   Elementary covering-space consequence of the free antipodal double cover in Joung--van Koert, Proposition 2.4, https://arxiv.org/abs/2407.19159v3.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- On a free invariant antipodal component, a least-period lifted orbit whose
half-period point is antipodal descends to a prime quotient binding. -/
theorem antipodal_double_cover_descends_to_prime_binding {μ c : ℝ}
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hanti : IsAntipodallyEquivariantFlow μ c φ)
    (hinv : IsAntipodallyInvariantComponent μ c)
    (hfree : IsAntipodallyFreeComponent μ c)
    (γ : PeriodicOrbit φ)
    (hdouble : IsAntipodalDoubleCover φ γ) :
    IsPrimeQuotientBinding φ hanti γ := by sorry

end BirkhoffGlobalSection
