-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_sgn_norm
-- name    : Formalism.L2.Pj.FundamentalDomainD5.sgn_norm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:46:39.724306+00:00
-- url     : https://prove2.me/theorems/5ed022fc-e307-53eb-9b8e-64abc9402bf4
-- title:
--   Fundamental Domain D5: sgn norm
-- statement:
--   The Fundamental Domain D5 construction uses the sgn norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/HQsmulRight.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/HQsmulRight.lean#L23-L25

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

theorem Formalism.L2.Pj.FundamentalDomainD5.sgn_norm (p : ℕ) (a : Fin r) : ‖sgn p a‖ = 1 := by sorry
