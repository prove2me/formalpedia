-- Prove2me | Theorems.Thm_Formalism_L2_Pj_wtZ_add
-- name    : Formalism.L2.Pj.wtZ_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:11.304416+00:00
-- url     : https://prove2.me/theorems/3eca068f-fdd2-460f-acea-cf1e1d04ed62
-- title:
--   Pj: wt Z add
-- statement:
--   The Pj construction uses the wt Z add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompData.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompData.lean#L13-L16

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem Formalism.L2.Pj.wtZ_add {E : Type} [Field E] (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) :
    wtZ (a + a') (n + n') = wtZ a n + wtZ a' n' := by sorry
