-- Prove2me | Theorems.Thm_Formalism_L2_PjFree_IsNormOn_of_goodOf
-- name    : Formalism.L2.PjFree.IsNormOn.of_goodOf
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:46:52.774429+00:00
-- url     : https://prove2.me/theorems/38c82f4a-6de9-49f7-bd6a-eb65444f174d
-- title:
--   Is Norm On: of good Of
-- statement:
--   The Is Norm On construction uses the of good Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/NormsFree.lean#L112-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/NormsFree.lean#L112-L114

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RulInst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PtFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_NormsFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.PjFree
open Formalism.L2.Pj
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

theorem Formalism.L2.PjFree.IsNormOn.of_goodOf {C : Submodule c.F (Rul Xo c)} {σ : c.F →+* ℂ} {N : Rul Xo c → ℝ}
    (h : IsNormOn C (goodOf c σ) N) : IsNormOn C σ N := by sorry
