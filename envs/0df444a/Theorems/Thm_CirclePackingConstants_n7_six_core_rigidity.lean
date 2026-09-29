-- Prove2me | Theorems.Thm_CirclePackingConstants_n7_six_core_rigidity
-- name    : CirclePackingConstants.n7_six_core_rigidity
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T00:37:41.86644+00:00
-- url     : https://prove2.me/theorems/c05080a8-4a3b-4ced-b7c6-a2e6c8fd9f24
-- title:
--   Six-core rigidity for the n=7 canonical configuration
-- statement:
--   The bounded signed displacement system and its eight contact inequalities force all twelve core displacements to vanish.
-- source:
--   Supplied circles_in_square_n7.pdf, §2 (six-core rigidity) and Appendix A.

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

theorem CirclePackingConstants.n7_six_core_rigidity
    (s r M eta : ℝ)
    (a b c e f g h i j k l t : ℝ)
    (hs : 0 < s)
    (hs_half : (1 : ℝ) / 2 < s)
    (hr0 : 0 ≤ r)
    (hr15 : (3 : ℝ) / 2 ≤ r)
    (hr18 : r ≤ (9 : ℝ) / 5)
    (hr2 : r ^ 2 = 3)
    (hrel : 2 * (1 - s) = r * s)
    (hM0 : 0 ≤ M)
    (hMsmall : M ≤ (1 : ℝ) / 100)
    (heta : eta = 4 * M ^ 2 / s)
    (hmax : M = max (|a|) (max (|b|) (max (|c|) (max (|e|) (max (|f|) (max (|g|)
      (max (|h|) (max (|i|) (max (|j|) (max (|k|) (max (|l|) (|t|))))))))))))
    (haL : -M ≤ a) (haU : a ≤ M)
    (hbL : -M ≤ b) (hbU : b ≤ M)
    (hcL : -M ≤ c) (hcU : c ≤ M)
    (heL : -M ≤ e) (heU : e ≤ M)
    (hfL : -M ≤ f) (hfU : f ≤ M)
    (hgL : -M ≤ g) (hgU : g ≤ M)
    (hhL : -M ≤ h) (hhU : h ≤ M)
    (hiL : -M ≤ i) (hiU : i ≤ M)
    (hjL : -M ≤ j) (hjU : j ≤ M)
    (hkL : -M ≤ k) (hkU : k ≤ M)
    (hlL : -M ≤ l) (hlU : l ≤ M)
    (htL : -M ≤ t) (htU : t ≤ M)
    (hwa : 0 ≤ a) (hwb : 0 ≤ b) (hwe : 0 ≤ e) (hwh : 0 ≤ h)
    (hwf : f ≤ 0) (hwt : t ≤ 0)
    (C1 : s ^ 2 ≤ (s + c - a) ^ 2 + (e - b) ^ 2)
    (C2 : s ^ 2 ≤ (h - a) ^ 2 + (s + i - b) ^ 2)
    (C3 : s ^ 2 ≤ (j - c) ^ 2 + (s + k - e) ^ 2)
    (C4 : s ^ 2 ≤ (s + j - h) ^ 2 + (k - i) ^ 2)
    (C5 : s ^ 2 ≤ (1 - s + f - c) ^ 2 + (s / 2 + g - e) ^ 2)
    (C6 : s ^ 2 ≤ (1 - s + f - j) ^ 2 + (-s / 2 + g - k) ^ 2)
    (C7 : s ^ 2 ≤ (s / 2 + l - h) ^ 2 + (1 - s + t - i) ^ 2)
    (C8 : s ^ 2 ≤ (-s / 2 + l - j) ^ 2 + (1 - s + t - k) ^ 2) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧
      h = 0 ∧ i = 0 ∧ j = 0 ∧ k = 0 ∧ l = 0 ∧ t = 0  := by sorry
