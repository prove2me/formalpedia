-- Prove2me | Theorems.Thm_Erdos287_four_layer_cover_iff_one_pattern_covers_two_edges
-- name    : Erdos287.four_layer_cover_iff_one_pattern_covers_two_edges
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T13:52:10.38067+00:00
-- url     : https://prove2.me/theorems/b49019ed-9cbe-56e4-9ac2-143c09c85541
-- title:
--   Exact pattern criterion for two triangles sharing an edge
-- statement:
--   Take four layers whose conflict graph has edges $01,02,12,13,23$. Give each layer a nonempty family of allowed retained patterns and suppose each edge endpoint can individually be retained. There is a choice of legal patterns with at least one retained endpoint on every edge exactly when some single legal pattern covers two distinct edges incident to its layer.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.four_layer_cover_iff_one_pattern_covers_two_edges (left right : Fin 5 → Fin 4) (posL posR : Fin 5 → ℕ)
    (F : Fin 4 → Finset (Finset ℕ))
    (hleft : left = ![0, 0, 1, 1, 2]) (hright : right = ![1, 2, 2, 3, 3])
    (hF : ∀ v, (F v).Nonempty)
    (hL : ∀ e, ∃ T ∈ F (left e), posL e ∈ T)
    (hR : ∀ e, ∃ T ∈ F (right e), posR e ∈ T) :
    (∃ C : Fin 4 → Finset ℕ, (∀ v, C v ∈ F v) ∧
      ∀ e, posL e ∈ C (left e) ∨ posR e ∈ C (right e)) ↔
    ∃ (v : Fin 4) (e f : Fin 5), e ≠ f ∧
      (v = left e ∨ v = right e) ∧ (v = left f ∨ v = right f) ∧
      ∃ T ∈ F v,
        (if v = left e then posL e else posR e) ∈ T ∧
        (if v = left f then posL f else posR f) ∈ T := by sorry
