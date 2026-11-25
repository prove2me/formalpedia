-- Prove2me | Theorems.Thm_Formalism_L2_PjFree_mulC_mem_sec
-- name    : Formalism.L2.PjFree.mulC_mem_sec
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:46:26.101649+00:00
-- url     : https://prove2.me/theorems/65d7f91c-e290-572a-abf8-c6912e3968dc
-- title:
--   Pj Free: mul C mem sec
-- statement:
--   The Pj Free construction uses the mul C mem sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CuspFree.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CuspFree.lean#L25-L26

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

theorem Formalism.L2.PjFree.mulC_mem_sec (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) {f g : Rul Xo c} (hf : f ∈ sec Xo c a n)
    (hg : g ∈ sec Xo c a' n') : mulC Xo c f g ∈ sec Xo c (a + a') (n + n') := by sorry
