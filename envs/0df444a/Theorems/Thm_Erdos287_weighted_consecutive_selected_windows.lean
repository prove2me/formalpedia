-- Prove2me | Theorems.Thm_Erdos287_weighted_consecutive_selected_windows
-- name    : Erdos287.weighted_consecutive_selected_windows
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T14:59:56.365155+00:00
-- url     : https://prove2.me/theorems/34780f5c-1eaf-4da4-ab58-841aacb7787a
-- title:
--   Reciprocal-weighted bound for fully selected windows
-- statement:
--   Let $D\subseteq[m,M]$ have reciprocal sum one, with $m,w>0$. Give each length-$w$ window inside the interval the reciprocal weight of its last position. The total weight of fully selected windows is at least the weight of all windows minus $w(\sum_{n=m}^M 1/n-1)$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.weighted_consecutive_selected_windows (D : Finset ℕ) (m M w : ℕ) (hm : 0 < m) (hw : 0 < w)
    (hD : D ⊆ Finset.Icc m M) (hsum : ∑ n ∈ D, (1 : ℝ) / n = 1) :
    let ends := Finset.Icc (m + w - 1) M
    let full := ends.filter (fun n => ∀ i ∈ Finset.range w, n - i ∈ D)
    (∑ n ∈ ends, (1 : ℝ) / n) - w * ((∑ n ∈ Finset.Icc m M, (1 : ℝ) / n) - 1) ≤
      ∑ n ∈ full, (1 : ℝ) / n := by sorry
