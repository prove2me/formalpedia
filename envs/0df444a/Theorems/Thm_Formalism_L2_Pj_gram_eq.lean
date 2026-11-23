-- Prove2me | Theorems.Thm_Formalism_L2_Pj_gram_eq
-- name    : Formalism.L2.Pj.gram_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:15:56.052638+00:00
-- url     : https://prove2.me/theorems/16985028-6868-46ee-9ac0-e5c9b6725ccb
-- title:
--   Pj: gram eq
-- statement:
--   The Pj construction uses the gram eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/UnifDom.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/UnifDom.lean#L12-L17

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

theorem Formalism.L2.Pj.gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G P = Pᵀ * G.map τ * P.map (starRingEnd ℂ) := by sorry
