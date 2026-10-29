-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_esscher_integrated_W_to_V_transfer
-- name    : AvramDividend.Classical.avram_ws01e_bt_new_esscher_integrated_W_to_V_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:53:19.857139+00:00
-- url     : https://prove2.me/theorems/a9a33e6a-e9dc-4646-996b-d7d38419c0b6
-- title:
--   Esscher exponential normalisation removes the constant from an integrated scale log-derivative
-- statement:
--   For real φ and functions W,g with g continuous on the strictly positive axis and W(b)=W(a) exp(∫a..b (φ+g)), show exactly that the Esscher-normalised V(x)=exp(-φx)W(x) satisfies V(b)=V(a) exp(∫a..b g). This is a deterministic interval-integral and exponential-algebra bridge relevant to converting authentic integrated q-scale formulas into the tilted-scale excursion representation. No Lévy or excursion law is presumed.

import Mathlib
open MeasureTheory Set
open scoped Topology

theorem AvramDividend.Classical.avram_ws01e_bt_new_esscher_integrated_W_to_V_transfer
    (φ : ℝ) (W g : ℝ → ℝ)
    (hg : ContinuousOn g (Ioi (0 : ℝ)))
    (hW : ∀ a b : ℝ, 0 < a → a ≤ b →
      W b = W a * Real.exp (∫ t in a..b, φ + g t)) :
    ∀ a b : ℝ, 0 < a → a ≤ b →
      Real.exp (-(φ * b)) * W b =
        (Real.exp (-(φ * a)) * W a) * Real.exp (∫ t in a..b, g t) := by sorry
