-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_sgn_conj
-- name    : Formalism.L2.Pj.FundamentalDomainD5.sgn_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:38.408108+00:00
-- url     : https://prove2.me/theorems/9c58d62d-9865-4c0b-8ee2-73eae71b4943
-- title:
--   Fundamental Domain D5: sgn conj
-- statement:
--   The Fundamental Domain D5 construction uses the sgn conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/HQsmulRight.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/HQsmulRight.lean#L19-L21

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

theorem Formalism.L2.Pj.FundamentalDomainD5.sgn_conj (p : ℕ) (a : Fin r) : conj (sgn p a) = sgn p a := by sorry
