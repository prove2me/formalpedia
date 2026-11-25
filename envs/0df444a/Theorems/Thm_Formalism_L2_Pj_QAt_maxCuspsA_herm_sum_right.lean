-- Prove2me | Theorems.Thm_Formalism_L2_Pj_QAt_maxCuspsA_herm_sum_right
-- name    : Formalism.L2.Pj.QAt.maxCuspsA_herm_sum_right
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:37:48.068003+00:00
-- url     : https://prove2.me/theorems/7f12f420-6121-5d19-95c8-815588003b0b
-- title:
--   QAt: max Cusps A herm sum right
-- statement:
--   The QAt construction uses the max Cusps A herm sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/MaximalCuspKernels/MaxCuspsPfA.lean#L208-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/MaximalCuspKernels/MaxCuspsPfA.lean#L208-L215

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

theorem Formalism.L2.Pj.QAt.maxCuspsA_herm_sum_right {ι : Type} (G : Matrix (Fin r) (Fin r) E) (s : Finset ι)
    (f : ι → Fin r → E) (x : Fin r → E) :
    herm G x (∑ i ∈ s, f i) = ∑ i ∈ s, herm G x (f i) := by sorry
