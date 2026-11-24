-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FJ_herm_g
-- name    : Formalism.L2.Pj.FJ.herm_g
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:07.422347+00:00
-- url     : https://prove2.me/theorems/cbdae9d1-c104-4360-a9bb-9a54efe4e4f2
-- title:
--   FJ: herm g
-- statement:
--   The FJ construction uses the herm g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RdOrbIntOfLatZ.lean#L104-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RdOrbIntOfLatZ.lean#L104-L107

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

theorem Formalism.L2.Pj.FJ.herm_g (X : Data E r) (τ : E →+* ℂ) : (cM (X.Gm.map τ))ᵀ = X.Gm.map τ := by sorry
