-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx2_eLat_eq
-- name    : Formalism.FourierDecayAlt.P.Jx2.eLat_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:08.690519+00:00
-- url     : https://prove2.me/theorems/94bf7cfa-6870-4a37-9f23-3f7a614e5b57
-- title:
--   Jx2: e Lat eq
-- statement:
--   The Jx2 construction uses the e Lat eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelSizesJointMean.lean#L579-L588
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelSizesJointMean.lean#L579-L588

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx2
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped nonZeroDivisors ComplexConjugate
open NumberField.mixedEmbedding MeasureTheory
open scoped Classical
noncomputable section
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
attribute [local instance] Formalism.FourierDecayAlt.P.Jx2.isEmptyReal

theorem Formalism.FourierDecayAlt.P.Jx2.eLat_eq (L : Submodule ℤ E) (c : ℝ) :
    eLat E L c = ZLattice.comap ℝ (S6.frameLat E L c) (ee E).toLinearMap := by sorry
