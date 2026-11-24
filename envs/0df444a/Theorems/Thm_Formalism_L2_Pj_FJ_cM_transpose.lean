-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FJ_cM_transpose
-- name    : Formalism.L2.Pj.FJ.cM_transpose
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:30.10223+00:00
-- url     : https://prove2.me/theorems/58ceb69f-1aee-4dfc-ad28-391cec3b77af
-- title:
--   FJ: c M transpose
-- statement:
--   The FJ construction uses the c M transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RdOrbIntOfLatZ.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RdOrbIntOfLatZ.lean#L27-L29

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
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
open ReciprocityTheory.ChartRestriction.G.FD NumberField Matrix
open scoped ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FJ
variable {r ρ : ℕ}

theorem Formalism.L2.Pj.FJ.cM_transpose {m n : Type} (A : Matrix m n ℂ) : cM Aᵀ = (cM A)ᵀ := by sorry
