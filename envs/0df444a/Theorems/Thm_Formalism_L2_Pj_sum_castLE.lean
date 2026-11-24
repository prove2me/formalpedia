-- Prove2me | Theorems.Thm_Formalism_L2_Pj_sum_castLE
-- name    : Formalism.L2.Pj.sum_castLE
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:44.416525+00:00
-- url     : https://prove2.me/theorems/dcff5323-775e-4cd0-b09b-eff4894d0713
-- title:
--   Pj: sum cast LE
-- statement:
--   The Pj construction uses the sum cast LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/UnifDom.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/UnifDom.lean#L24-L30

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnifDom
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
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem Formalism.L2.Pj.sum_castLE {R : Type} [AddCommMonoid R] {i n : ℕ} (h : i ≤ n) (f : Fin n → R)
    (hf : ∀ c : Fin n, i ≤ (c : ℕ) → f c = 0) : ∑ c, f c = ∑ c : Fin i, f (Fin.castLE h c) := by sorry
