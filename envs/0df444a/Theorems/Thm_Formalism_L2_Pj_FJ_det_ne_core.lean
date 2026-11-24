-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FJ_det_ne_core
-- name    : Formalism.L2.Pj.FJ.det_ne_core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:38.090085+00:00
-- url     : https://prove2.me/theorems/1e165566-f05b-491e-ae44-1aa58cae9d2c
-- title:
--   FJ: det ne core
-- statement:
--   The FJ construction uses the det ne core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RdOrbIntOfLatZ.lean#L57-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RdOrbIntOfLatZ.lean#L57-L73

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

theorem Formalism.L2.Pj.FJ.det_ne_core (g : Matrix (Fin r) (Fin r) ℂ) (F : Matrix (Fin r) (Fin ρ) ℂ)
    (β : Matrix (Fin ρ) (Fin ρ) ℂ) (hiso : Fᵀ * g * cM F = 0) :
    (1 + F * β * (g * cM F)ᵀ).det ≠ 0 := by sorry
