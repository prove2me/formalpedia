-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FJ_zAct_mem_dom
-- name    : Formalism.L2.Pj.FJ.zAct_mem_dom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:40.929428+00:00
-- url     : https://prove2.me/theorems/5491dfc8-4fdc-47b0-8c65-9807cfcc04c9
-- title:
--   FJ: z Act mem dom
-- statement:
--   The FJ construction uses the z Act mem dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RdOrbIntOfLatZ.lean#L136-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RdOrbIntOfLatZ.lean#L136-L165

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

theorem Formalism.L2.Pj.FJ.zAct_mem_dom (X : Data E r) (cu : CuspFD X ρ) (hb : ∀ k, IsSkew (zBas X cu k))
    (t : Fin (nZ X ρ) → ℝ) (x : Frame X.Ψ r) (hx : x ∈ X.dom) : zAct X cu t x ∈ X.dom := by sorry
