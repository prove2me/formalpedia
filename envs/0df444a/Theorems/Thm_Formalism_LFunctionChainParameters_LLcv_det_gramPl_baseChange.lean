-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_det_gramPl_baseChange
-- name    : Formalism.LFunctionChainParameters.LLcv.det_gramPl_baseChange
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:21.02978+00:00
-- url     : https://prove2.me/theorems/d09ba8af-f7f3-4446-9f2f-440962c58416
-- title:
--   LLcv: det gram Pl base Change
-- statement:
--   The LLcv construction uses the det gram Pl base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TruncatedLatticeHolds.lean#L625-L640
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TruncatedLatticeHolds.lean#L625-L640

import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LLcv
open Formalism.HN Formalism.HermitianLatticesTheory Formalism.LFunctionChainParameters.slopeLatticeData
open scoped Matrix
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]

theorem Formalism.LFunctionChainParameters.LLcv.det_gramPl_baseChange (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) {j : ℕ} (e : Fin j → V) (g : Matrix (Fin j) (Fin j) K)
    (him : (gramPl b X v e).det.im = 0) :
    (gramPl b X v (fun a => ∑ c, g c a • e c)).det.re =
      v g.det ^ 2 * (gramPl b X v e).det.re := by sorry
