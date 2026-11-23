-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BoxOne_geom_prod_sum_le
-- name    : Formalism.FourierDecayAlt.P.BoxOne.geom_prod_sum_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:57:26.608112+00:00
-- url     : https://prove2.me/theorems/b8ef6fde-084f-43db-a686-d20650dff07b
-- title:
--   Box One: geom prod sum le
-- statement:
--   The Box One construction uses the geom prod sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BoxOne.lean#L8-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BoxOne.lean#L8-L32

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_SqrtAbsNormLeProd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BoxOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BoxOne
open NumberField Finset

theorem Formalism.FourierDecayAlt.P.BoxOne.geom_prod_sum_le {ι : Type} [Fintype ι] (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (T : Finset (ι → ℕ)) :
    ∑ k ∈ T, ∏ i, q ^ (k i) ≤ (1 / (1 - q)) ^ Fintype.card ι := by sorry
