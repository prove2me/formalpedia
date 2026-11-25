-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Misc_isSquare_of_hensel
-- name    : Formalism.FrobeniusOrbits.Misc.isSquare_of_hensel
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:35:28.200743+00:00
-- url     : https://prove2.me/theorems/a52c70e1-bc7f-501c-94af-e1f6f4a8e774
-- title:
--   Misc: is Square of hensel
-- statement:
--   The Misc construction uses the is Square of hensel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/OrderOfSignGroupDvdTwo.lean#L18-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/OrderOfSignGroupDvdTwo.lean#L18-L31

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Misc

theorem Formalism.FrobeniusOrbits.Misc.isSquare_of_hensel (p : ℕ) [Fact p.Prime] (c a : ℤ)
    (h : ‖((a ^ 2 + c : ℤ) : ℤ_[p])‖ < ‖((2 * a : ℤ) : ℤ_[p])‖ ^ 2) :
    IsSquare (-(c : ℤ_[p])) := by sorry
