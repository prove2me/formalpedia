-- Prove2me | Theorems.Thm_BesbesZeevi_Nonparametric_fact1_JD_lower_bound
-- name    : BesbesZeevi.Nonparametric.fact1_JD_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T14:30:21.828356+00:00
-- url     : https://prove2.me/theorems/10a4ac52-f186-40d7-86c2-67d16636dbcb
-- title:
--   Fact 1: $\inf_{\lambda\in\mathcal L}J^D(x,T\mid\lambda)\ge m^D=m\min\{T,x/M\}>0$
-- statement:
--   Let $x>0$ and $T>0$, and let $\mathcal L=\mathcal L(M,\underline K,\overline K,m)$ be the nonparametric demand class. Put $T'=\min\{T,x/M\}$ and $m^D=mT'$. Then $m^D>0$, and every $\lambda\in\mathcal L$ satisfies
--
--   $$
--   J^D(x,T\mid\lambda)\ \ge\ m^D .
--   $$
--
--   This keeps the benchmark in the denominator of the regret bounded away from zero, uniformly over the class.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 27 (PDF 29), Fact 1

import Mathlib
import Definitions.Def_BesbesZeevi_Nonparametric_Model

open MeasureTheory

namespace BesbesZeevi.Nonparametric

/-- Fact 1, p. 27: `inf_{λ ∈ 𝓛} J^D(x, T | λ) ≥ m^D`, where `m^D = m T' > 0` and
`T' = min{T, x/M}`. -/
theorem fact1_JD_lower_bound (P : PriceSet) (L : DemandClass) (x T : ℝ) (hx : 0 < x) (hT : 0 < T) :
    0 < L.m * min T (x / L.M) ∧
      ∀ lam : ℝ → ℝ, L.Mem P lam → L.m * min T (x / L.M) ≤ JD P lam x T := by sorry

end BesbesZeevi.Nonparametric
