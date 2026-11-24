-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_h_qsmul_left
-- name    : Formalism.L2.Pj.FundamentalDomainD5.h_qsmul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:12.962096+00:00
-- url     : https://prove2.me/theorems/269fe0a3-ac5b-4f46-b08a-eed8a13a77c9
-- title:
--   Fundamental Domain D5: h qsmul left
-- statement:
--   The Fundamental Domain D5 construction uses the h qsmul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/HQsmulRight.lean#L83-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/HQsmulRight.lean#L83-L85

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

theorem Formalism.L2.Pj.FundamentalDomainD5.h_qsmul_left (q : ℚ) (x y : Fin r → K) : S.h (q • x) y = (q : K) * S.h x y := by sorry
