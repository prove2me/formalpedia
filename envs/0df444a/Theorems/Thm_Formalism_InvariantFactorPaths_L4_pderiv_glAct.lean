-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_pderiv_glAct
-- name    : Formalism.InvariantFactorPaths.L4.pderiv_glAct
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:34:39.690071+00:00
-- url     : https://prove2.me/theorems/eae7c797-008c-4600-9fa6-da8d2f225e47
-- title:
--   L4: pderiv gl Act
-- statement:
--   The L4 construction uses the pderiv gl Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/ResInto.lean#L188-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/ResInto.lean#L188-L200

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
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

theorem Formalism.InvariantFactorPaths.L4.pderiv_glAct (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (a b c : Fin r)
    (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    pderiv (Fin.last K, c) (glAct p LL (K + 1) a b x) =
      glAct p LL (K + 1) a b (pderiv (Fin.last K, c) x) + (if a = c then pderiv (Fin.last K, b) x else 0) := by sorry
