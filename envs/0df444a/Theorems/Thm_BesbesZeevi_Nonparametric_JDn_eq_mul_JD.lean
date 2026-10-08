-- Prove2me | Theorems.Thm_BesbesZeevi_Nonparametric_JDn_eq_mul_JD
-- name    : BesbesZeevi.Nonparametric.JDn_eq_mul_JD
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T14:30:06.150269+00:00
-- url     : https://prove2.me/theorems/7ee2c1b9-d687-4c28-9e7b-4b4ac7049e36
-- title:
--   Scaling of the deterministic relaxation: $J^D_n(x,T\mid\lambda)=nJ^D(x,T\mid\lambda)$
-- statement:
--   Let $J^D(x,T\mid\lambda)$ be the value of the deterministic relaxation (5). Let $J^D_n(x,T\mid\lambda)$ be the same value under the scaling (11): inventory $nx$ and demand function $n\lambda$. Then for every demand function $\lambda$ and every positive integer $n$,
--
--   $$
--   J^D_n(x,T\mid\lambda)=n\,J^D(x,T\mid\lambda).
--   $$
--
--   This identity lets the regret in the market of size $n$ be compared with the unscaled benchmark.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 12 (PDF 14), §4.3; also Fact 1, p. 27 (PDF 29)

import Mathlib
import Definitions.Def_BesbesZeevi_Nonparametric_Model

open MeasureTheory

namespace BesbesZeevi.Nonparametric

/-- §4.3, p. 12 (also Fact 1, p. 27): under the scaling (11), `J^D_n(x, T | λ) = n J^D(x, T | λ)`. -/
theorem JDn_eq_mul_JD (P : PriceSet) (lam : ℝ → ℝ) (x T : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    JDn P lam x T n = (n : ℝ) * JD P lam x T := by sorry

end BesbesZeevi.Nonparametric
