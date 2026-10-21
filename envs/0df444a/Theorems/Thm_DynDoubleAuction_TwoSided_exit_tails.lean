-- Prove2me | Theorems.Thm_DynDoubleAuction_TwoSided_exit_tails
-- name    : DynDoubleAuction.TwoSided.exit_tails
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:41.55208+00:00
-- url     : https://prove2.me/theorems/77722bc0-0357-4936-9faa-bfa7cb818da7
-- title:
--   Proof of Theorem 5.3 — low and high exit tails
-- statement:
--   Let $w^1=\underline w_0+\bar v\sqrt{8T\log T}$ satisfy the theorem's upper-side condition, and let $1\le t\le T^*$, where $T^*=T+1-(\bar v+\underline w_0+2\bar v\sqrt{8T\log T})/\mu$. The probabilities of first entering the low and high regions obey
--
--   $$\Pr(\underline\tau\le t)\le\exp\!\left(-\frac{(w^1-\underline w_0)^2}{8t\bar v^2}\right),\qquad\Pr(\bar\tau\le t)\le\exp\!\left(-\frac{(\bar w^t-\bar v-w^1)^2}{8t\bar v^2}\right).$$
--
--   These two estimates control the inefficient periods in Theorem 5.3.
--
--   **Formalization Note** The first intermediate equality printed on p. 30 is used as an inclusion; the displayed outer probability inequality is what is formalized. The theorem uses integer $t$ below the real threshold $T^*$.
-- source:
--   Balseiro, Mirrokni, Paes Leme & Zuo, Dynamic Double Auctions: Towards First Best, SSRN 3213460 (version of November 15, 2018), p. 30, proof of Theorem 5.3

import Mathlib
import Definitions.Def_DynDoubleAuction_TwoSided_Model

namespace DynDoubleAuction.TwoSided

open MeasureTheory Filter Topology

/-- The two exit-time tails used in the proof of Theorem 5.3. -/
theorem exit_tails {n : ℕ} (M : Market n) (hM : Standing M)
    (T t : ℕ) (hT : 2 ≤ T) (ht : 1 ≤ t ∧ (t : ℝ) ≤ Tstar M T)
    (hside : initialPromise M T ≤ wbar M T 1 -
      M.vbar * (1 + Real.sqrt (8 * (T : ℝ) * Real.log T))) :
    (valueLaw M).real {vs | tauLow M T (initialPromise M T) vs ≤ t} ≤
        Real.exp (-(initialPromise M T - wlow M) ^ 2 /
          (8 * (t : ℝ) * M.vbar ^ 2)) ∧
    (valueLaw M).real {vs | tauHigh M T (initialPromise M T) vs ≤ t} ≤
        Real.exp (-(wbar M T t - M.vbar - initialPromise M T) ^ 2 /
          (8 * (t : ℝ) * M.vbar ^ 2)) := by sorry
end DynDoubleAuction.TwoSided
