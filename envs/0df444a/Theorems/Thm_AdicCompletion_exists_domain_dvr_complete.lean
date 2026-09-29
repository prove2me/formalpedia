-- Prove2me | Theorems.Thm_AdicCompletion_exists_domain_dvr_complete
-- name    : AdicCompletion.exists_domain_dvr_complete
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-24T16:16:56.727455+00:00
-- url     : https://prove2.me/theorems/321b13ea-c50b-4685-a62c-50be4c5cfb83
-- title:
--   The completion of a Dedekind domain at a nonzero prime is a complete DVR
-- statement:
--   Let $A$ be a Dedekind domain and let $\mathfrak p$ be a nonzero prime ideal of $A$. The inverse-limit completion
--
--   $$\widehat A_{\mathfrak p}=\varprojlim_{n\ge0} A/\mathfrak p^n$$
--
--   is an integral domain and a discrete valuation ring, and is complete with respect to its own maximal ideal.
--
--   This gives the algebraic local coefficient ring used when passing from field-valued Galois representations to integral lattices. The existing ring structure on the inverse limit is retained.
-- source:
--   Consequence of the existing proved DVR completion theorem, https://prove2.me/theorems/a0e3aec5-3479-5c44-9927-bcd6e6f2d355, and the existing proved localization/completion comparison, https://prove2.me/theorems/d1ec29e0-26c9-5e94-b475-5ce731ee73ca. The fact that localization of a Dedekind domain at a nonzero prime is a DVR is Mathlib.RingTheory.DedekindDomain.Dvr, IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain.

import Theorems.Thm_IsDiscreteValuationRing_adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete
import Theorems.Thm_Ideal_IsMaximal_exists_adicCompletion_localization_ringEquiv
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.AdicCompletion.Topology

/-!
Completion of a Dedekind domain at a nonzero prime, by localization to a DVR.

Exact Prove2Me inputs:
* `IsDiscreteValuationRing.adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete`,
  theorem `a0e3aec5-3479-5c44-9927-bcd6e6f2d355`;
* `Ideal.IsMaximal.exists_adicCompletion_localization_ringEquiv`,
  theorem `d1ec29e0-26c9-5e94-b475-5ce731ee73ca`.

Mathlib supplies the DVR property of the localization and transfer of domain,
DVR, and adic completeness along the completion comparison.
-/

set_option autoImplicit false
noncomputable section

open IsLocalRing

namespace AdicCompletion

/-- Completing a Dedekind domain at a nonzero prime gives a complete DVR. -/
theorem exists_domain_dvr_complete
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : Ideal R) [P.IsPrime] (hP : P ≠ ⊥) :
    ∃ (_ : IsDomain (AdicCompletion P R))
      (_ : IsDiscreteValuationRing (AdicCompletion P R)),
      IsAdicComplete (maximalIdeal (AdicCompletion P R)) (AdicCompletion P R) := by
  sorry

end AdicCompletion
