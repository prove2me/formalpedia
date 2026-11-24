-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_st_Q_update
-- name    : Formalism.InvariantFactorPaths.KP.LL.st_Q_update
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:37:04.38626+00:00
-- url     : https://prove2.me/theorems/d0fbaedb-c6e3-401b-bd1f-220642cf4f09
-- title:
--   LL: st Q update
-- statement:
--   The LL construction uses the st Q update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/StepTie.lean#L150-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/StepTie.lean#L150-L156

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_StepTie
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
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (D : BlockData N)
variable {D}

theorem Formalism.InvariantFactorPaths.KP.LL.st_Q_update (k : ℕ) (kk : Fin D.T.t) (j : Fin D.T.t → ℕ) (jp l : ℕ) :
    stQ p (r := r) D k kk (Function.update j kk l) jp = stQ p D k kk j jp := by sorry
