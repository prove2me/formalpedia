-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_Uop_supp
-- name    : Formalism.InvariantFactorPaths.L4.Uop_supp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:03.285557+00:00
-- url     : https://prove2.me/theorems/5ae23991-0c28-468a-8b95-2f325ef3cb21
-- title:
--   L4: Uop supp
-- statement:
--   The L4 construction uses the Uop supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RaisingKeepsEarlyLetters.lean#L76-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RaisingKeepsEarlyLetters.lean#L76-L98

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

theorem Formalism.InvariantFactorPaths.L4.Uop_supp [NeZero r] (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (c k : ℤ)
    (Cs : Finset (Fin r)) (a : Fin r) (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hF : F ∈ restrictSupport ℚ_[p] {m : Fin (K + 1) × Fin r →₀ ℕ | wt LL (K + 1) 0 m ≤ k}) :
    Uop p LL c Cs a F ∈ restrictSupport ℚ_[p]
      {m : Fin (K + 1) × Fin r →₀ ℕ | wt LL (K + 1) 0 m ≤ k + (if a = 0 then 1 else 0)} := by sorry
