-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_embVec_qsmul
-- name    : Formalism.L2.Pj.FundamentalDomainD5.embVec_qsmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:49.231816+00:00
-- url     : https://prove2.me/theorems/dd9ae1d0-dec5-44c5-a046-584e3b0590a7
-- title:
--   Fundamental Domain D5: emb Vec qsmul
-- statement:
--   The Fundamental Domain D5 construction uses the emb Vec qsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/HQsmulRight.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/HQsmulRight.lean#L35-L37

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

theorem Formalism.L2.Pj.FundamentalDomainD5.embVec_qsmul (τ : K →+* ℂ) (q : ℚ) (x : Fin r → K) : embVec τ (q • x) = (q : ℂ) • embVec τ x := by sorry
