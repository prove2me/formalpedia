-- Prove2me | Theorems.Thm_Formalism_L2_Pj_ex_add
-- name    : Formalism.L2.Pj.ex_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:34:34.096747+00:00
-- url     : https://prove2.me/theorems/c0d9a62d-f67a-4645-980f-2eba9f67ff73
-- title:
--   Pj: ex add
-- statement:
--   The Pj construction uses the ex add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/EmbKCoe.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/EmbKCoe.lean#L17-L19

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_EmbKCoe
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
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem Formalism.L2.Pj.ex_add (Dw : Datum H) (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) :
    ex Dw (a + a') (n + n') = ex Dw a n + ex Dw a' n' := by sorry
