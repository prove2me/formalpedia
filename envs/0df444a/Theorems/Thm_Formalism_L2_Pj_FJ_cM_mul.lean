-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FJ_cM_mul
-- name    : Formalism.L2.Pj.FJ.cM_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:15:51.466073+00:00
-- url     : https://prove2.me/theorems/4cbf2db7-5e35-4914-9e1b-295aa7bba914
-- title:
--   FJ: c M mul
-- statement:
--   The FJ construction uses the c M mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RdOrbIntOfLatZ.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RdOrbIntOfLatZ.lean#L22-L25

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

theorem Formalism.L2.Pj.FJ.cM_mul {m n o : Type} [Fintype n] (A : Matrix m n ℂ) (B : Matrix n o ℂ) :
    cM (A * B) = cM A * cM B := by sorry
