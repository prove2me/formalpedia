-- Prove2me | Theorems.Thm_Formalism_HC_An_induces_of
-- name    : Formalism.HC.An.induces_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:31.795947+00:00
-- url     : https://prove2.me/theorems/0895b1b1-07ed-4d11-92d1-3c7c8d031648
-- title:
--   An: induces of
-- statement:
--   The An construction uses the induces of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean#L68-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean#L68-L76

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_PrimePairSizeCondition
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Analytic
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
open Formalism.HC.An

theorem Formalism.HC.An.induces_of {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    Induces (PChar.of χ).χ (fun a => χ (a : ZMod N)) N := by sorry
