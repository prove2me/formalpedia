-- Prove2me | Theorems.Thm_CachonCoord_BaseStock_eq_28
-- name    : CachonCoord.BaseStock.eq_28
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:45:56.291966+00:00
-- url     : https://prove2.me/theorems/cd58bde8-cc4c-4d4b-91a3-78aeb19ccbcb
-- title:
--   Eq. (28), p. 72 — expected inventory is the integral of the demand cdf
-- statement:
--   Let $D_r$ be nonnegative lead-time demand with distribution function $F_r$ and density $f_r$, and let $I_r(y)=\mathbb E[(y-D_r)^+]$ be expected inventory. For every $y\ge0$,
--   $$I_r(y)=\int_0^y (y-x)f_r(x)\,dx=\int_0^y F_r(x)\,dx.$$
--
--   This gives the distribution-function form of the inventory term in every cost formula of §6.7.1.
--
--   **Formalization Note** Expected inventory is defined by expectation; the displayed integral is a theorem. The model records finite mean and the section's continuity and strict-increase assumptions on $F_r$.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.7.1, Eq. (28), p. 72

import Mathlib
import Definitions.Def_CachonCoord_BaseStock_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.BaseStock

/-- Cachon (2003), §6.7.1, Eq. (28), p. 72: expected on-hand inventory is the
integral of the lead-time demand distribution function. -/
theorem eq_28 (M : Model) :
    ∀ y : ℝ, 0 ≤ y →
      M.I y = ∫ x in (0 : ℝ)..y, (y - x) * M.density x ∧
      M.I y = ∫ x in (0 : ℝ)..y, M.F x := by sorry

end CachonCoord.BaseStock
