-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_source_cell_jump_chord_bound
-- name    : AvramDividend.Classical.avram_chat24_source_cell_jump_chord_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:19:15.939146+00:00
-- url     : https://prove2.me/theorems/60cb099c-a8c0-4155-9817-fdd35d7ffa2b
-- title:
--   Source cell jump chords satisfy the Lipschitz bound
-- statement:
--   Independent coefficient estimate extracted mathematically from the complete 184-line proof of parent 1eea7159-587a-416f-ae50-9a71b706b90c. The accepted atomic-prefix interval identity proves m>=0. Monotonicity of K and band bounds give a-d*h<=V-m<=V<=b. Small mesh puts both arguments in the Lipschitz interval; the quotient has norm <=L including m=0, and discounting cannot increase it. The statement retains precisely the summability, source, order, band and Lipschitz hypotheses used, without any parent assumption or cycle.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_chat24_source_cell_jump_chord_bound
    (f K : ℝ≥0 → ℝ) (v d a b q : ℝ) (B : ℝ≥0)
    (ha : 0 < a) (hq : 0 ≤ q)
    (hf_down : ∀ r : ℝ≥0, 0 < r → f r ≤ Function.leftLim f r)
    (hK : Monotone K)
    (hsum : Summable (fun r : ℝ≥0 =>
      if 0 < r ∧ r ≤ B then Function.leftLim f r - f r else 0))
    (hsource : ∀ t : ℝ≥0, t ≤ B → f t = (t : ℝ) * d -
      ∑' r : ℝ≥0, if 0 < r ∧ r ≤ t then Function.leftLim f r - f r else 0)
    (s t : ℝ≥0) (hst : s ≤ t) (htB : t ≤ B)
    (hs : v + f s - K s ∈ Icc a b) (ht : v + f t - K t ∈ Icc a b)
    (h m : ℝ) (hgap : (t : ℝ) - (s : ℝ) = h)
    (hmdef : m = d * h - (f t - f s))
    (hsmall : d * h < min (a / 2) 1)
    (w : ℝ → ℝ) (L : ℝ≥0)
    (hLip : LipschitzOnWith L w (Icc (a / 2) (b + 1))) :
    ‖Real.exp (-(q * (t : ℝ))) *
      ((w (v + f s - K s - m) - w (v + f s - K s)) / m)‖ ≤ (L : ℝ) := by sorry
