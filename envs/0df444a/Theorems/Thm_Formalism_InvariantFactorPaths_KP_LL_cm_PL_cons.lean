-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_cm_PL_cons
-- name    : Formalism.InvariantFactorPaths.KP.LL.cm_PL_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:36:15.243662+00:00
-- url     : https://prove2.me/theorems/055a61f8-fe3d-4198-be02-40d2f1c39e49
-- title:
--   LL: cm PL cons
-- statement:
--   The LL construction uses the cm PL cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/LatticeLinearHolds.lean#L150-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/LatticeLinearHolds.lean#L150-L151

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeLinearHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] {D : BlockData N}

theorem Formalism.InvariantFactorPaths.KP.LL.cm_PL_cons (i : Fin D.T.t) (L : List (Fin D.T.t)) (j : Fin D.T.t → ℕ) (jp : ℕ)
    (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) : PL p D (i :: L) j jp x = Pt p D j jp i (PL p D L j jp x) := by sorry
