-- Prove2me | Theorems.Thm_Formalism_L2_PjFree_mem_cusp
-- name    : Formalism.L2.PjFree.mem_cusp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:13.933036+00:00
-- url     : https://prove2.me/theorems/e35f7b12-ffb3-408e-a373-81741156ebfd
-- title:
--   Pj Free: mem cusp
-- statement:
--   The Pj Free construction uses the mem cusp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CuspFree.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CuspFree.lean#L19-L21

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

theorem Formalism.L2.PjFree.mem_cusp (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) :
    f ∈ cusp Xo c U a n ↔ f ∈ sec Xo c a n ∧ ∀ σ : c.F →+* ℂ, GoodEmb c σ → rdU (U σ) f ∈ holSub (U σ).X (laU (U σ) a n) := by sorry
