-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_NewtonPolygonValuation_val_prod
-- name    : Formalism.CyclotomicNorms.NewtonPolygonValuation.val_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:53.618799+00:00
-- url     : https://prove2.me/theorems/c634144f-7b8b-42a3-ab9b-7b2b050102c2
-- title:
--   Newton Polygon Valuation: val prod
-- statement:
--   The Newton Polygon Valuation construction uses the val prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/Newton.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/Newton.lean#L13-L18

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_Newton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.NewtonPolygonValuation
variable {L : Type} [Field L] (v : AddValuation L (WithTop ℝ))

theorem Formalism.CyclotomicNorms.NewtonPolygonValuation.val_prod {ι : Type*} (s : Finset ι) (g : ι → L) :
    v (∏ i ∈ s, g i) = ∑ i ∈ s, v (g i) := by sorry
