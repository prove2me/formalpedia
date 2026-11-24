-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_cor_tsum_cmp
-- name    : Formalism.IncomingBounds.cor_tsum_cmp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:41.364927+00:00
-- url     : https://prove2.me/theorems/47bd5480-9d0a-43fa-9917-6e0f54bd420b
-- title:
--   Incoming Bounds: cor tsum cmp
-- statement:
--   The Incoming Bounds construction uses the cor tsum cmp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/BaseTermLeTopTerm.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/BaseTermLeTopTerm.lean#L20-L24

import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_LevelTail
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_BaseTermLeTopTerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds

theorem Formalism.IncomingBounds.cor_tsum_cmp {f g b : ℕ → ℝ} (hg0 : ∀ e, 0 ≤ g e) (hgf : ∀ e, g e ≤ f e)
    (hfb : ∀ e, f e ≤ b e) (hb : Summable b) : ∑' e, g e ≤ ∑' e, f e := by sorry
