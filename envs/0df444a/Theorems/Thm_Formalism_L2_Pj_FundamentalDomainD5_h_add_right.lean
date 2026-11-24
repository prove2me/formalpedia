-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_h_add_right
-- name    : Formalism.L2.Pj.FundamentalDomainD5.h_add_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:37.276464+00:00
-- url     : https://prove2.me/theorems/8dc3851f-a333-4cf0-a3fe-4cc0e668beed
-- title:
--   Fundamental Domain D5: h add right
-- statement:
--   The Fundamental Domain D5 construction uses the h add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/HQsmulRight.lean#L70-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/HQsmulRight.lean#L70-L71

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

theorem Formalism.L2.Pj.FundamentalDomainD5.h_add_right (x y y' : Fin r → K) : S.h x (y + y') = S.h x y + S.h x y' := by sorry
