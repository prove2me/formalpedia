-- Prove2me | Theorems.Thm_EulerMascheroni_Sondow_scaled_integral_bounds_eventually
-- name    : EulerMascheroni.Sondow.scaled_integral_bounds_eventually
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-04T13:57:54.688975+00:00
-- url     : https://prove2.me/theorems/f748b0d2-3096-4fdb-9f9a-47a00952982f
-- title:
--   $0<d_{2n}I_n<2^{-n}$ for all large $n$
-- statement:
--   For all sufficiently large $n$, $0<d_{2n}I_n<2^{-n}$, where $I_n$ is Sondow's double integral and $d_{2n}=\operatorname{lcm}(1,\dots,2n)$.
--
--   This eventual form is all Sondow's criterion needs, and unlike the all-$n$ version it needs only the asymptotic prime number theorem, not explicit Rosser–Schoenfeld bounds.
-- source:
--   J. Sondow, Criteria for irrationality of Euler's constant, Proc. AMS 131 (2003) 3335–3344, arXiv:math/0209070, proof of Thm. 2.

import Definitions.Def_eulerMascheroni_sondow
open EulerMascheroni.Sondow

theorem EulerMascheroni.Sondow.scaled_integral_bounds_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n →
      0 < (d (2*n) : ℝ) * I n ∧ (d (2*n) : ℝ) * I n < (1/2 : ℝ)^n := by sorry
