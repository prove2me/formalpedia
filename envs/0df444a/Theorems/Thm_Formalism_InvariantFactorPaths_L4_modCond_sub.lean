-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_modCond_sub
-- name    : Formalism.InvariantFactorPaths.L4.modCond_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:00:02.013046+00:00
-- url     : https://prove2.me/theorems/075c2006-0b8f-44fd-bc0b-f8c74d2fad7f
-- title:
--   L4: mod Cond sub
-- statement:
--   The L4 construction uses the mod Cond sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersModP.lean#L181-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersModP.lean#L181-L184

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (LL : Letters N) (j : ℕ)
variable (M : WithTop ℤ)

theorem Formalism.InvariantFactorPaths.L4.modCond_sub (f g : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hf : ModCond p LL j M f)
    (hg : ModCond p LL j M g) : ModCond p LL j M (f - g) := by sorry
