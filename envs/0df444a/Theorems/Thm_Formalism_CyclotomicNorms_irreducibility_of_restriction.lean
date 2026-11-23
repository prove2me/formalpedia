-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_irreducibility_of_restriction
-- name    : Formalism.CyclotomicNorms.irreducibility_of_restriction
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:56:36.019911+00:00
-- url     : https://prove2.me/theorems/5b6844e5-2de0-4aa4-b38c-45e044608adf
-- title:
--   Cyclotomic Norms: irreducibility of restriction
-- statement:
--   The Cyclotomic Norms construction uses the irreducibility of restriction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L640-L641
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L640-L641

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section

theorem Formalism.CyclotomicNorms.irreducibility_of_restriction (hR : Formalism.CyclotomicNorms.Restriction) : Formalism.CyclotomicNorms.IrreducibilityCriterion := by sorry
