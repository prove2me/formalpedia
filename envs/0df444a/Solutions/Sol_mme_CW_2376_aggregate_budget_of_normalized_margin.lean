-- Prove2me | solution 1 for mme_CW_2376_aggregate_budget_of_normalized_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T21:52:57.471297+00:00
-- url     : https://prove2.me/submissions/0fe06227-ca86-4f4e-9a60-fe68b6b4df60

import Mathlib

set_option autoImplicit false

/-- Reinsert the common target-vertex and hash-fiber factors after proving the
normalized outer CW collision margin. -/
theorem solution
    (N p T S D Dstar : ℕ) (V loss : ℝ)
    (hN : 1 ≤ N) (hV : 0 ≤ V)
    (hT : (T : ℝ) = V * (Dstar : ℝ))
    (hmargin :
      (p : ℝ) ^ 2 * loss + 3 * (Dstar : ℝ) * (D : ℝ) ≤
        (Dstar : ℝ) * (S : ℝ)) :
    (p : ℝ) ^ (N + 1) * (V * loss) +
        3 * (T : ℝ) * (D : ℝ) * (p : ℝ) ^ (N - 1) ≤
      (T : ℝ) * (S : ℝ) * (p : ℝ) ^ (N - 1) := by
  have hpow :
      (p : ℝ) ^ (N + 1) = (p : ℝ) ^ 2 * (p : ℝ) ^ (N - 1) := by
    rw [show N + 1 = 2 + (N - 1) by omega, pow_add]
  calc
    (p : ℝ) ^ (N + 1) * (V * loss) +
          3 * (T : ℝ) * (D : ℝ) * (p : ℝ) ^ (N - 1) =
        (V * (p : ℝ) ^ (N - 1)) *
          ((p : ℝ) ^ 2 * loss +
            3 * (Dstar : ℝ) * (D : ℝ)) := by
              rw [hpow, hT]
              ring
    _ ≤ (V * (p : ℝ) ^ (N - 1)) *
          ((Dstar : ℝ) * (S : ℝ)) := by
            gcongr
    _ = (T : ℝ) * (S : ℝ) * (p : ℝ) ^ (N - 1) := by
      rw [hT]
      ring
