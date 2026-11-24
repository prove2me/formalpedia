-- Prove2me | Theorems.Thm_Formalism_HC_jacobi_neg_recip
-- name    : Formalism.HC.jacobi_neg_recip
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:10:59.993307+00:00
-- url     : https://prove2.me/theorems/b97e972b-27d6-4232-8af7-a303f1bfd8be
-- title:
--   HC: jacobi neg recip
-- statement:
--   The HC construction uses the jacobi neg recip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostFacts.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostFacts.lean#L15-L23

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ExistsOpenNormalOrderOf
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits

theorem Formalism.HC.jacobi_neg_recip {r p : ℕ} (hr : r % 4 = 3) (hp : p % 2 = 1) :
    jacobiSym (-(r : ℤ)) p = jacobiSym (p : ℤ) r := by sorry
