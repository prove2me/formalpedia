-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_NewtonPolygonValuation_val_zeta_sub_one
-- name    : Formalism.CyclotomicNorms.NewtonPolygonValuation.val_zeta_sub_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:55:11.722816+00:00
-- url     : https://prove2.me/theorems/de9a35ec-8fcb-45b1-a9f4-e215b5247044
-- title:
--   Newton Polygon Valuation: val zeta sub one
-- statement:
--   The Newton Polygon Valuation construction uses the val zeta sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/Newton.lean#L50-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/Newton.lean#L50-L86

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

theorem Formalism.CyclotomicNorms.NewtonPolygonValuation.val_zeta_sub_one {ℓ j : ℕ} (hℓ : ℓ.Prime) (hj : 1 ≤ j) (hv : v (ℓ : L) = wt 1) {z : L}
    (hz : IsPrimitiveRoot z (ℓ ^ j)) :
    v (z - 1) = wt (1 / ((ℓ ^ j).totient : ℝ)) := by sorry
