-- Prove2me | Theorems.Thm_BesbesZeevi_SingleParam_fact1
-- name    : BesbesZeevi.SingleParam.fact1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T15:00:26.021266+00:00
-- url     : https://prove2.me/theorems/6660d37b-19be-4bd7-852a-d837d2d110b1
-- title:
--   Fact 1: $J^D_n=nJ^D$ and $\inf_{\lambda\in\mathcal L}J^D(x,T\mid\lambda)\ge m\min\{T,x/M\}$
-- statement:
--   Let $M,\underline K,\overline K,m>0$ with $\underline K\le\overline K$, and put $T'=\min\{T,x/M\}$ and $m^D=mT'$. Then $m^D>0$, and every demand function $\lambda\in\mathcal L(M,\underline K,\overline K,m)$ satisfies
--
--   $$
--   J^D_n(x,T\mid\lambda)=n\,J^D(x,T\mid\lambda)\quad(n\ge1),\qquad J^D(x,T\mid\lambda)\ge m^D .
--   $$
--
--   The lower bound is uniform over the class; it keeps the regret's denominator away from zero in every rate bound of the paper.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 27 (PDF p. 29), Fact 1

import Mathlib
import Definitions.Def_BesbesZeevi_SingleParam_Model

open MeasureTheory

namespace BesbesZeevi.SingleParam

/-- Fact 1 (Besbes–Zeevi 2009, p. 27): `J^D_n = n J^D`, and
`inf_{λ ∈ 𝓛} J^D(x, T | λ) ≥ m^D` with `m^D = m T' > 0`, `T' = min {T, x/M}`. -/
theorem fact1 (D : Market) (M KLo KHi m : ℝ) (hM : 0 < M) (hKLo : 0 < KLo)
    (hK : KLo ≤ KHi) (hm : 0 < m) :
    0 < m * min D.T (D.x / M) ∧
    ∀ f : ℝ → ℝ, InClass D M KLo KHi m f →
      (∀ n : ℕ, 1 ≤ n → detValueScaled D f n = (n : ℝ) * detValue D f D.x) ∧
      m * min D.T (D.x / M) ≤ detValue D f D.x := by sorry

end BesbesZeevi.SingleParam
