-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstRecord_geometric_ENNReal_eq_ofReal_ratio
-- name    : AvramDividend.Classical.firstRecord_geometric_ENNReal_eq_ofReal_ratio
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:43:26.912198+00:00
-- url     : https://prove2.me/theorems/a9bb6d0c-4973-4522-99de-4dcc91722be8
-- title:
--   Convert first-record ENNReal geometric ratio to the real finite quotient
-- statement:
--   For ε≥0 and 0≤p<1, the closed form of the extended-nonnegative geometric renewal payment, ε·p/(1-p) in ENNReal arithmetic, is exactly the ofReal embedding of the ordinary real quotient. This is the algebraic conversion needed to match the stopped renewal scale finite-difference bounds after first-passage survival estimates have been established.
-- source:
--   Mathlib ENNReal.ofReal_sub, ENNReal.ofReal_inv_of_pos, ENNReal.ofReal_mul and ring.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Real

theorem AvramDividend.Classical.firstRecord_geometric_ENNReal_eq_ofReal_ratio
    (ε p : ℝ) (hε : 0 ≤ ε) (hp : 0 ≤ p) (hplt : p < 1) :
    ENNReal.ofReal ε * (ENNReal.ofReal p * (1 - ENNReal.ofReal p)⁻¹) =
      ENNReal.ofReal (ε * p / (1 - p)) := by sorry
