-- Prove2me | Theorems.Thm_EulerMascheroni_Sondow_d_le_pow_eventually
-- name    : EulerMascheroni.Sondow.d_le_pow_eventually
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-04T13:57:44.760986+00:00
-- url     : https://prove2.me/theorems/e329181a-b36b-4603-b35e-b66c360cd7b6
-- title:
--   $\operatorname{lcm}(1,\dots,m)\le b^m$ eventually, for every $b>e$
-- statement:
--   For every real $b>e$, $d_m=\operatorname{lcm}(1,\dots,m)\le b^m$ for all large $m$.
--
--   Since $\log d_m=\psi(m)$, this is the prime number theorem $\psi(m)\sim m$ (only the upper bound is needed).
-- source:
--   Hardy–Wright, An Introduction to the Theory of Numbers, Thm. 6 and §22.2 ($\psi(x)=\log\operatorname{lcm}(1..x)$, $\psi(x)\sim x$).

import Definitions.Def_eulerMascheroni_sondow
open EulerMascheroni.Sondow

theorem EulerMascheroni.Sondow.d_le_pow_eventually (b : ℝ) (hb : Real.exp 1 < b) :
    ∀ᶠ m : ℕ in Filter.atTop, (d m : ℝ) ≤ b ^ m := by sorry
