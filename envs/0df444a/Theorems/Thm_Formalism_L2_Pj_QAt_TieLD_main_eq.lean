-- Prove2me | Theorems.Thm_Formalism_L2_Pj_QAt_TieLD_main_eq
-- name    : Formalism.L2.Pj.QAt.TieLD.main_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:35:20.643816+00:00
-- url     : https://prove2.me/theorems/fe16a1ed-0da1-49c5-8e8f-53262463959d
-- title:
--   Tie LD: main eq
-- statement:
--   The Tie LD construction uses the main eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/LenDescentOfLengthBaseChangeLocal.lean#L175-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/LenDescentOfLengthBaseChangeLocal.lean#L175-L276

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

theorem Formalism.L2.Pj.QAt.TieLD.main_eq (hL : Formalism.LatticeBaseChangeAlt.LengthBaseChangeLocal)
    {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (M : Submodule (𝓞 K) V) (hMfg : M.FG) (W : Submodule K V) {ρ : ℕ} (θ : Fin ρ → M)
    (la : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K₁)) (hw : LiesOver w la) :
    lenW w M W θ = (w.asIdeal.ramificationIdx (𝓞 K) : ℕ∞) *
      lenLa la (QuotMW M W ⧸ Submodule.span (𝓞 K)
        (Set.range fun j => (Submodule.Quotient.mk (θ j) : QuotMW M W))) := by sorry
