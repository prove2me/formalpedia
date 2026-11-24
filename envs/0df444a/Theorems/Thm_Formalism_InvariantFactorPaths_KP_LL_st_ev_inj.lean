-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_st_ev_inj
-- name    : Formalism.InvariantFactorPaths.KP.LL.st_ev_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:08.348747+00:00
-- url     : https://prove2.me/theorems/6fb11dbe-9bb5-490f-9c31-7f6b55e7d3cb
-- title:
--   LL: st ev inj
-- statement:
--   The LL construction uses the st ev inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/StepTie.lean#L162-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/StepTie.lean#L162-L164

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

theorem Formalism.InvariantFactorPaths.KP.LL.st_ev_inj (kk : Fin D.T.t) : Function.Injective (ev (r := r) D kk) := by sorry
