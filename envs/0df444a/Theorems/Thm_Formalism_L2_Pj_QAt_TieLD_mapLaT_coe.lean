-- Prove2me | Theorems.Thm_Formalism_L2_Pj_QAt_TieLD_mapLaT_coe
-- name    : Formalism.L2.Pj.QAt.TieLD.mapLaT_coe
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:30:44.296505+00:00
-- url     : https://prove2.me/theorems/e87f58d2-fc8e-43e2-af7a-7b259a2498ed
-- title:
--   Tie LD: map La T coe
-- statement:
--   The Tie LD construction uses the map La T coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/LenDescentOfLengthBaseChangeLocal.lean#L94-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/LenDescentOfLengthBaseChangeLocal.lean#L94-L109

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreSt
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LengthBaseChange
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_LenDescentOfLengthBaseChangeLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt
open Formalism.L2.Pj.QAt.TieLD
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct
attribute [local instance] TieLDA.modT TieLDA.modR
variable {K K₁ : Type} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
attribute [local instance] algCT
attribute [local instance] locT
attribute [local instance] dvrT
attribute [local instance] dvrLa
attribute [local instance] algLaK
attribute [local instance] towerLaK
attribute [local instance] fracLaK

theorem Formalism.L2.Pj.QAt.TieLD.mapLaT_coe (la : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K₁))
    (hw : LiesOver w la) (r : Localization.AtPrime la.asIdeal) :
    ((mapLaT la w hw r : Tw w) : K₁) =
      algebraMap K K₁ (algebraMap (Localization.AtPrime la.asIdeal) K r) := by sorry
