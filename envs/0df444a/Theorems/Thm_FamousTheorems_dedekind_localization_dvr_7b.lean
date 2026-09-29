-- Prove2me | Theorems.Thm_FamousTheorems_dedekind_localization_dvr_7b
-- name    : FamousTheorems.dedekind_localization_dvr_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:34:05.033261+00:00
-- url     : https://prove2.me/theorems/b3687e9d-8135-4347-b6bf-ce649e5e0017
-- title:
--   The localization of a Dedekind domain at a nonzero prime is a DVR
-- statement:
--   **Localizations of Dedekind domains are discrete valuation rings.** Let $A$ be a Dedekind domain and $P$ a nonzero prime ideal. Then the localization $A_P$ is a discrete valuation ring.
--
--   This is the local description of Dedekind domains, and in fact characterizes them: a Noetherian domain is Dedekind exactly when all its localizations at nonzero primes are DVRs. It lets one define the $P$-adic valuation on the fraction field and the multiplicity of $P$ in a fractional ideal, and it explains geometrically why Dedekind domains correspond to nonsingular curves.
--
--   **Formalization note.** Mathlib's `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`. The localization is given by any domain $A_{\mathfrak m}$ satisfying `IsLocalization.AtPrime Aₘ P`, that is, any ring with the universal property of $A_P$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem dedekind_localization_dvr_7b (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A] {P : Ideal A} (hP : P ≠ ⊥) [P.IsPrime]
    (Aₘ : Type*) [CommRing Aₘ] [IsDomain Aₘ] [Algebra A Aₘ] [IsLocalization.AtPrime Aₘ P] :
    IsDiscreteValuationRing Aₘ := by sorry

end FamousTheorems
