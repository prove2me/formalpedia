-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FJ_gram_eq
-- name    : Formalism.L2.Pj.FJ.gram_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:46.989022+00:00
-- url     : https://prove2.me/theorems/95fd57d7-6095-4283-b0c6-3c19189f4980
-- title:
--   FJ: gram eq
-- statement:
--   The FJ construction uses the gram eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RdOrbIntOfLatZ.lean#L97-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RdOrbIntOfLatZ.lean#L97-L102

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem Formalism.L2.Pj.FJ.gram_eq (X : Data E r) (τ : E →+* ℂ) (A : Matrix (Fin r) (Fin r) ℂ) :
    gram τ X.Gm A = Aᵀ * X.Gm.map τ * cM A := by sorry
