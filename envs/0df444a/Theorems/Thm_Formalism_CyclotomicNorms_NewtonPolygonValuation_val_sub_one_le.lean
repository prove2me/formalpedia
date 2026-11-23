-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_NewtonPolygonValuation_val_sub_one_le
-- name    : Formalism.CyclotomicNorms.NewtonPolygonValuation.val_sub_one_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:59.873798+00:00
-- url     : https://prove2.me/theorems/dd72d828-26a1-49c7-b0ee-78d6fa4d4fc5
-- title:
--   Newton Polygon Valuation: val sub one le
-- statement:
--   The Newton Polygon Valuation construction uses the val sub one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/Newton.lean#L40-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/Newton.lean#L40-L48

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

theorem Formalism.CyclotomicNorms.NewtonPolygonValuation.val_sub_one_le {ζ : L} {N : ℕ} (hN : 0 < N) (hζ : ζ ^ N = 1) (i : ℕ) :
    v (ζ - 1) ≤ v (ζ ^ i - 1) := by sorry
