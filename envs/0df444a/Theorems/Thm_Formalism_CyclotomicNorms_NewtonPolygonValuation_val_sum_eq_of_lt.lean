-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_NewtonPolygonValuation_val_sum_eq_of_lt
-- name    : Formalism.CyclotomicNorms.NewtonPolygonValuation.val_sum_eq_of_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:55:00.460846+00:00
-- url     : https://prove2.me/theorems/a9fc8092-5ed2-4af7-afe8-413913822c67
-- title:
--   Newton Polygon Valuation: val sum eq of lt
-- statement:
--   The Newton Polygon Valuation construction uses the val sum eq of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/Newton.lean#L88-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/Newton.lean#L88-L92

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

theorem Formalism.CyclotomicNorms.NewtonPolygonValuation.val_sum_eq_of_lt {ι : Type*} [DecidableEq ι] {s : Finset ι} {g : ι → L} {i₀ : ι}
    (hi : i₀ ∈ s) (h0 : v (g i₀) ≠ ⊤) (hlt : ∀ i ∈ s.erase i₀, v (g i₀) < v (g i)) :
    v (∑ i ∈ s, g i) = v (g i₀) := by sorry
