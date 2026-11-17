-- Prove2me | Theorems.Thm_APFPaper5_K4_not_fixedByProducts_of_rateFree
-- name    : APFPaper5.K4.not_fixedByProducts_of_rateFree
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T15:50:29.198486+00:00
-- url     : https://prove2.me/theorems/7300441c-ab4f-4656-b737-6ce440000058
-- title:
--   not fixedByProducts of rateFree
-- statement:
--   Result: not fixedByProducts of rateFree. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem not_fixedByProducts_of_rateFree (admPart : Set Held2) (admJoint : Set Joint)
--       (hfree : ∀ h ∈ admPart, RateFree h)
--       (hrec : jointAdd (pair ⟨1, 0, 0, 0⟩ ⟨1, 0, 0, 0⟩) (pair ⟨0, 0, 1, 0⟩ ⟨0, 0, 1, 0⟩) ∈ admJoint) :
--       ¬ FixedByProducts admPart admJoint
--   ```
--
--   Module context and limits: FixedByProducts is an uninstalled candidate interpretation, not derived from the by-levels record statement. Together with admission of the specified recombination it implies an admitted non-rate-free part state. No physical rates, tensor closure or K3/K4 completion are established.
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K4_fixed_by_products_needs_rates:70; pullbacks v39; source SHA-256 583146169cf7a84c385e7cb035352532da4bccfc85494116585412468df9cb7e']

import Definitions.Def_APFPaper5_K4_fixed_by_products_needs_rates_Vocabulary
import Theorems.Thm_APFPaper5_K4_reading_zero_on_products_is_zero
import Theorems.Thm_APFPaper5_K4_compositeOnly_is_product_of_rates
import Theorems.Thm_APFPaper5_K4_sums_of_books_differ_in_compositeOnly
import Theorems.Thm_APFPaper5_K4_compositeOnly_needs_own_record
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace APFPaper5.K4
end APFPaper5.K4
open APFPaper5
open APFPaper5.K4
open APFPaper5.K3

theorem APFPaper5.K4.not_fixedByProducts_of_rateFree (admPart : Set Held2) (admJoint : Set Joint)
    (hfree : ∀ h ∈ admPart, RateFree h)
    (hrec : jointAdd (pair ⟨1, 0, 0, 0⟩ ⟨1, 0, 0, 0⟩) (pair ⟨0, 0, 1, 0⟩ ⟨0, 0, 1, 0⟩) ∈ admJoint) :
    ¬ FixedByProducts admPart admJoint := by sorry
