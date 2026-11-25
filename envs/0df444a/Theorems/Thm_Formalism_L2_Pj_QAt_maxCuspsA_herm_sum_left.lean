-- Prove2me | Theorems.Thm_Formalism_L2_Pj_QAt_maxCuspsA_herm_sum_left
-- name    : Formalism.L2.Pj.QAt.maxCuspsA_herm_sum_left
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:36:52.595568+00:00
-- url     : https://prove2.me/theorems/15530767-45ba-4739-9370-f4b34a821f16
-- title:
--   QAt: max Cusps A herm sum left
-- statement:
--   The QAt construction uses the max Cusps A herm sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/MaximalCuspKernels/MaxCuspsPfA.lean#L199-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/MaximalCuspKernels/MaxCuspsPfA.lean#L199-L206

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

theorem Formalism.L2.Pj.QAt.maxCuspsA_herm_sum_left {ι : Type} (G : Matrix (Fin r) (Fin r) E) (s : Finset ι)
    (f : ι → Fin r → E) (y : Fin r → E) :
    herm G (∑ i ∈ s, f i) y = ∑ i ∈ s, herm G (f i) y := by sorry
