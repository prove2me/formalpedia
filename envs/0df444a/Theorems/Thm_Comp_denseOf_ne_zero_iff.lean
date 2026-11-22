-- Prove2me | Theorems.Thm_Comp_denseOf_ne_zero_iff
-- name    : Comp.denseOf_ne_zero_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:48:07.36279+00:00
-- url     : https://prove2.me/theorems/a7bee103-6c5a-4881-88c5-5612fc1f7805
-- title:
--   Comp: dense Of ne zero iff
-- statement:
--   **The support of a sparse row.** With no negative weights there is nothing to cancel and with
--       no zero weights nothing to discount, so the densified vector is nonzero at `s'` exactly when
--       some entry mentions `s'` -- a statement about the row's *keys*, with the weights gone.
--
--       Both hypotheses earn their place. Drop nonnegativity and two entries could cancel; drop
--       nonzero-ness and a listed successor could carry no mass. An induction, with
--       `add_ne_zero_iff_of_nonneg` at each step.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L225-L257
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L225-L257

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.denseOf_ne_zero_iff (n : ℕ) (dist : List (ℕ × ℚ)) (s' : Fin n) :
    (∀ p ∈ dist, 0 ≤ p.2) → (∀ p ∈ dist, p.2 ≠ 0) →
      (denseOf n dist s' ≠ 0 ↔ ∃ p ∈ dist, p.1 = (s' : ℕ)) := by sorry
