-- Prove2me | Theorems.Thm_Formalism_HC_cycHom_apply
-- name    : Formalism.HC.cycHom_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:55:14.513487+00:00
-- url     : https://prove2.me/theorems/a6925a19-a104-47af-a79f-ee97c11a1efb
-- title:
--   HC: cyc Hom apply
-- statement:
--   The HC construction uses the cyc Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameCyclicGenerator.lean#L94-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameCyclicGenerator.lean#L94-L97

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

theorem Formalism.HC.cycHom_apply (e : ℕ) (i : ZMod (2 ^ e)) :
    cycHom e i = Additive.ofMul (hcl e (u5 (e + 2)) ^ i.val) := by sorry
