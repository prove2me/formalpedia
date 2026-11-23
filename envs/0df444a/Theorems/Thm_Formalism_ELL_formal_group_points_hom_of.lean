-- Prove2me | Theorems.Thm_Formalism_ELL_formal_group_points_hom_of
-- name    : Formalism.ELL.formal_group_points_hom_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:02.030205+00:00
-- url     : https://prove2.me/theorems/529df304-445e-4102-bd13-f641b438a893
-- title:
--   ELL: formal group points hom of
-- statement:
--   The ELL construction uses the formal group points hom of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L1217-L1226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L1217-L1226

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section

theorem Formalism.ELL.formal_group_points_hom_of (hU : Formalism.ELL.WSubstUnique.{u}) (hS : Formalism.ELL.WChordSubst.{u})
    (hFG : Formalism.ELL.WFormalGroup.{u}) (hPar : Formalism.ELL.FormalGroupPointsParametrisation.{u}) : Formalism.ELL.FormalGroupPointsHomomorphism.{u} := by sorry
