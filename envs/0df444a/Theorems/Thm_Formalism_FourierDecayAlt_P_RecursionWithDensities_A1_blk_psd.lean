-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_blk_psd
-- name    : Formalism.FourierDecayAlt.P.RecursionWithDensities.A1.blk_psd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:12.992707+00:00
-- url     : https://prove2.me/theorems/21af7499-7e79-4d38-a640-58a7109d5f16
-- title:
--   A1: blk psd
-- statement:
--   The A1 construction uses the blk psd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean#L222-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean#L222-L246

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Classical
variable {E : Type} [Field E] [DecidableEq E]

theorem Formalism.FourierDecayAlt.P.RecursionWithDensities.A1.blk_psd (D : TA.Data E) (Sg : ℕ → ℕ → Finset E) (hNZ : NZSg Sg) (hK : AxK D) (i s : ℕ)
    (hs : 1 ≤ s) (hsi : s ≤ i) (hi : i ≤ D.r + 1) (t : E) (ht : t ≠ 0) :
    PSDOn (PT Sg (i - s)) (fun h h' => D.K i (TA.ext h s t) (TA.ext h' s t)) := by sorry
