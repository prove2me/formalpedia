-- Prove2me | solution 1 for p2m_path_dual_decay
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:11:09.48364+00:00
-- url     : https://prove2.me/submissions/1ddd5809-175a-434c-a5bf-2af397946eef

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
import Theorems.Thm_p2m_dual_decay
open Matrix VanderbeiLP.PathFollowing
open scoped VanderbeiLP.PathFollowing

theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (δ r t : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (s d : ℕ → PDPoint m n) (K : ℕ)
    (hstep : ∀ k ≤ K, IsPathFollowingStep A b c δ r (s k) (d k) (s (k + 1)))
    (hθ : ∀ k ≤ K, t ≤ stepLength r (s k) (d k)) :
    ∀ k ≤ K, norm1 (dualInfeas A c (s k)) ≤ (1 - t) ^ k * norm1 (dualInfeas A c (s 0)) :=
  p2m_dual_decay A b c δ r t hδ0 hδ1 hr0 hr1 s d K hstep hθ
