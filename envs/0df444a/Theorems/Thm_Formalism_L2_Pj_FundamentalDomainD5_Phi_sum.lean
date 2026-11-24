-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_Phi_sum
-- name    : Formalism.L2.Pj.FundamentalDomainD5.Phi_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:42.37497+00:00
-- url     : https://prove2.me/theorems/5be1a00b-2db0-42b1-9efb-342d32ff8c33
-- title:
--   Fundamental Domain D5: Phi sum
-- statement:
--   The Fundamental Domain D5 construction uses the Phi sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/HQsmulRight.lean#L59-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/HQsmulRight.lean#L59-L61

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

theorem Formalism.L2.Pj.FundamentalDomainD5.Phi_sum (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ) {κ : Type} (s : Finset κ)
    (x : κ → Fin r → K) : Phi σ Q (∑ j ∈ s, x j) = ∑ j ∈ s, Phi σ Q (x j) := by sorry
