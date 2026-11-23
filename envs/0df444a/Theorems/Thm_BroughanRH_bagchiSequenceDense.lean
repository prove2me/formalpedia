-- Prove2me | Theorems.Thm_BroughanRH_bagchiSequenceDense
-- name    : BroughanRH.bagchiSequenceDense
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:21:28.360711+00:00
-- url     : https://prove2.me/theorems/6147edc4-a759-4497-9fc1-4b31ab4236bb
-- title:
--   Density in Bagchi’s sequence space
-- statement:
--   The same fractional-part sequences have dense linear span in the full weighted complex sequence space. The Lean sequence index starts at zero for the first component.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II §3.4 (Bagchi). https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem bagchiSequenceDense :
    let w (n : ℕ) := ((n+1 : ℕ) : ℝ) * (n+2 : ℕ)
    ∀ f : ℕ → ℂ, Summable (fun n : ℕ => ‖f n‖^2 / w n) →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ a : Fin N → ℂ,
        let g (n : ℕ) := ‖f n - ∑ j, a j *
          ((Int.fract (((n+1 : ℕ) : ℝ)/(j.val+1 : ℕ)) : ℝ) : ℂ)‖^2 / w n
        Summable g ∧ (∑' n : ℕ, g n) < ε := by sorry

end BroughanRH
