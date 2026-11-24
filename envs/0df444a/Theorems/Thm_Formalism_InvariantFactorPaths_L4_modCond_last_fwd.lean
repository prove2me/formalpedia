-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_modCond_last_fwd
-- name    : Formalism.InvariantFactorPaths.L4.modCond_last_fwd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:12.131221+00:00
-- url     : https://prove2.me/theorems/0278b997-db7b-4dd5-83f5-498d42170fbf
-- title:
--   L4: mod Cond last fwd
-- statement:
--   The L4 construction uses the mod Cond last fwd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersModP.lean#L268-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersModP.lean#L268-L291

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
variable (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) (j : ℕ) (M : WithTop ℤ)

theorem Formalism.InvariantFactorPaths.L4.modCond_last_fwd (hj : K + 1 ≤ j) (hv : LL.vec (Fin.last K) = true) (c' : Fin r)
    (g g' : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hg : ModCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) g) (hg' : ModCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) g') :
    ModCond p LL j M (X (Fin.last K, c') * g + X (Fin.last K, (0 : Fin r)) * g') := by sorry
