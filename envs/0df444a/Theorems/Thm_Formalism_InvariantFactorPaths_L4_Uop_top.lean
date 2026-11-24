-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_Uop_top
-- name    : Formalism.InvariantFactorPaths.L4.Uop_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:17.363961+00:00
-- url     : https://prove2.me/theorems/ed56015d-1c25-48c6-ba20-9bad0af5db4b
-- title:
--   L4: Uop top
-- statement:
--   The L4 construction uses the Uop top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RaisingKeepsEarlyLetters.lean#L100-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RaisingKeepsEarlyLetters.lean#L100-L118

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}

theorem Formalism.InvariantFactorPaths.L4.Uop_top [NeZero r] (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (c : ℤ)
    (G : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (h0 : glAct p LL (K + 1) 0 0 G = ((c : ℤ) : ℚ_[p]) • G)
    (hb : ∀ b : Fin r, b ≠ 0 → glAct p LL (K + 1) 0 b G = 0) : Uop p LL c univ 0 G = 0 := by sorry
