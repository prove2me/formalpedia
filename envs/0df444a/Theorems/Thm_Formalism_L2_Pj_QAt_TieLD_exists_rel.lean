-- Prove2me | Theorems.Thm_Formalism_L2_Pj_QAt_TieLD_exists_rel
-- name    : Formalism.L2.Pj.QAt.TieLD.exists_rel
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:35:42.389849+00:00
-- url     : https://prove2.me/theorems/62dfcc5a-da6f-4c93-9337-b42b718b2ded
-- title:
--   Tie LD: exists rel
-- statement:
--   The Tie LD construction uses the exists rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/LenDescentOfLengthBaseChangeLocal.lean#L129-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/LenDescentOfLengthBaseChangeLocal.lean#L129-L173

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

theorem Formalism.L2.Pj.QAt.TieLD.exists_rel (la : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K₁))
    (hw : LiesOver w la) :
    ∃ (ϖ : Localization.AtPrime la.asIdeal) (ϖ₁ : Tw w) (u : (Tw w)ˣ), Irreducible ϖ ∧
      Irreducible ϖ₁ ∧ mapLaT la w hw ϖ = u * ϖ₁ ^ (w.asIdeal.ramificationIdx (𝓞 K)) := by sorry
