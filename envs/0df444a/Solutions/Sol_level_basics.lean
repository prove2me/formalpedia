-- Prove2me | solution 1 for level_basics
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:23:13.401044+00:00
-- url     : https://prove2.me/submissions/b9330658-3a3e-42ab-9d82-c12cb82fc8af

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnLevBasics
import Theorems.Thm_PI_QnLevBasicsW_level_group_ellipticity
import Theorems.Thm_PI_QnLevBasicsW_level_group_homomorphism
import Theorems.Thm_PI_QnLevBasicsW_level_group_isotropic_vector
import Theorems.Thm_PI_QnLevBasicsW_level_group_nilpotent
import Theorems.Thm_PI_QnLevBasicsW_level_group_unitary_hermitian
import Theorems.Thm_PI_QnLevBasicsW_level_group_unitary_weyl


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : Formalism.QuantumDeterminants.LevHom ∧ Formalism.QuantumDeterminants.LevUH ∧ Formalism.QuantumDeterminants.LevN ∧ Formalism.QuantumDeterminants.LevUW ∧ Formalism.QuantumDeterminants.LevWb ∧ Formalism.QuantumDeterminants.LevEll :=
  ⟨PI.QnLevBasicsW.level_group_homomorphism, PI.QnLevBasicsW.level_group_unitary_hermitian, PI.QnLevBasicsW.level_group_nilpotent,
    PI.QnLevBasicsW.level_group_unitary_weyl, PI.QnLevBasicsW.level_group_isotropic_vector, PI.QnLevBasicsW.level_group_ellipticity⟩
