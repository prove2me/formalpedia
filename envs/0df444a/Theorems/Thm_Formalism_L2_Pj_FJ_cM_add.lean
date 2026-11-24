-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FJ_cM_add
-- name    : Formalism.L2.Pj.FJ.cM_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:18.32104+00:00
-- url     : https://prove2.me/theorems/a17c8797-0155-48ad-ab7a-02fd57ecb5fb
-- title:
--   FJ: c M add
-- statement:
--   The FJ construction uses the c M add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RdOrbIntOfLatZ.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RdOrbIntOfLatZ.lean#L31-L33

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

theorem Formalism.L2.Pj.FJ.cM_add {m n : Type} (A B : Matrix m n ℂ) : cM (A + B) = cM A + cM B := by sorry
