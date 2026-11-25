-- Prove2me | Theorems.Thm_Formalism_L2_Pj_QAt_maxCuspsA_beta_map
-- name    : Formalism.L2.Pj.QAt.maxCuspsA_beta_map
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:38:07.118833+00:00
-- url     : https://prove2.me/theorems/6d97bfa0-dff9-4f3f-bde7-efed28750f35
-- title:
--   QAt: max Cusps A beta map
-- statement:
--   The QAt construction uses the max Cusps A beta map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/MaximalCuspKernels/MaxCuspsPfA.lean#L255-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/MaximalCuspKernels/MaxCuspsPfA.lean#L255-L297

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.FD NumberField Matrix Formalism.L2.Pj.FJ Complex
open scoped ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem Formalism.L2.Pj.QAt.maxCuspsA_beta_map (X : Data E r) (la : Wt X.Ψ r) (η : Fin ρ → E) (a : E)
    (ha : cc a = a) (τ : X.Ψ) :
    (mcBeta X la η a).map τ.1 =
      (((ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters.per X la a τ : ℝ) : ℂ) * (-(I * X.c τ))) • mcMηc τ.1 η := by sorry
