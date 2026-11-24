-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_X_mul_pol
-- name    : Formalism.InvariantFactorPaths.L4.X_mul_pol
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:14.163472+00:00
-- url     : https://prove2.me/theorems/395dc1dd-3e49-425a-8c36-65eb3212fe91
-- title:
--   L4: X mul pol
-- statement:
--   The L4 construction uses the X mul pol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RaisingKeepsEarlyLetters.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RaisingKeepsEarlyLetters.lean#L46-L51

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

theorem Formalism.InvariantFactorPaths.L4.X_mul_pol (LL : Letters (K + 1)) (a : Fin r) (o : ℕ) (G : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hG : G ∈ Pol p r (setLast LL o)) : X (Fin.last K, a) * G ∈ Pol p r (setLast LL (o + 1)) := by sorry
