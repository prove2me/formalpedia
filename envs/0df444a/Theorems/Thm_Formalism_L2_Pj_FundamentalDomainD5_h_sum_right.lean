-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_h_sum_right
-- name    : Formalism.L2.Pj.FundamentalDomainD5.h_sum_right
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:00.085177+00:00
-- url     : https://prove2.me/theorems/e5662ad7-ac55-49aa-9f18-e22bb7a1fa0c
-- title:
--   Fundamental Domain D5: h sum right
-- statement:
--   The Fundamental Domain D5 construction uses the h sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/HQsmulRight.lean#L98-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/HQsmulRight.lean#L98-L100

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_RhoDotSelf
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_HQsmulRight
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
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FundamentalDomainD5
open NumberField Matrix ComplexConjugate ReciprocityTheory.MultiplicativeHeights
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {r : ℕ}
variable (S : HermForm K r)

theorem Formalism.L2.Pj.FundamentalDomainD5.h_sum_right {κ : Type} (s : Finset κ) (x : Fin r → K) (y : κ → Fin r → K) :
    S.h x (∑ j ∈ s, y j) = ∑ j ∈ s, S.h x (y j) := by sorry
