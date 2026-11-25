-- Prove2me | solution 1 for operators_commute_translations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:15:22.002429+00:00
-- url     : https://prove2.me/submissions/d0de6138-59b1-4dd8-b394-d66c2445781c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OperatorsCommuteTranslationsOfLeftRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OfFnProdIntertwine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_LyQminorLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OperatorModel
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_AAInvTrans
import Theorems.Thm_AAInvW_algebra_aa
import Theorems.Thm_AAInvW_algebra_aa_vector
import Theorems.Thm_AAInvW_hpk_involution
import Theorems.Thm_AAInvW_left_aa
import Theorems.Thm_AAInvW_operator_model
import Theorems.Thm_AAInvW_operators_commute_translations_of_left_right
import Theorems.Thm_AAInvW_rightAA_of
import Theorems.Thm_AAInvW_subset_inverse_column
import Theorems.Thm_AAInvW_subset_row_star
import Theorems.Thm_AAInvW_subset_upper_hessenberg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : Formalism.FourierDecayAlt.C3.OperatorsCommuteTranslations :=
  AAInvW.operators_commute_translations_of_left_right AAInvW.left_aa
    (AAInvW.rightAA_of AAInvW.operator_model AAInvW.algebra_aa AAInvW.algebra_aa_vector AAInvW.hpk_involution
      AAInvW.subset_upper_hessenberg AAInvW.subset_inverse_column AAInvW.subset_row_star)
    AAInvW.subset_upper_hessenberg
