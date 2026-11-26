-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_finitecap_diagonal_cash_bound_of_contDiffOn_closed_cap_neighborhood
-- name    : AvramDividend.Classical.gaussian_finitecap_diagonal_cash_bound_of_contDiffOn_closed_cap_neighborhood
-- status  : Open
-- author  : @scuba8684
-- created : 2026-11-26T06:58:21.448804+00:00
-- url     : https://prove2.me/theorems/d19a8155-6cf8-4ec3-a8ce-66e19602cbf2
-- title:
--   Gaussian finite-cap stopped cash bound for a candidate smooth on a neighborhood of the closed cap interval
-- statement:
--   Consider the original Gaussian-only dividend problem with positive drift, a positive finite cap $C$, and positive initial reserve $xle C$. Let $v$ be twice continuously differentiable on an open interval containing the entire reserve interval $[0,C]$. Assume $vge0$, $v'ge1$, and $Gamma v-qvle0$ on that closed interval.
--
--   Prove that every admissible strategy has expected discounted Stieltjes dividend cash through the original ruin clock clipped at the positive integer horizon $n$ at most $v(x)$. The conclusion retains the original payment-time convention, including the atom at time zero. This formulation isolates smooth controlled Gaussian verification. The derivatives are bounded on the compact reserve interval by smoothness on its neighborhood. Right dividend jumps that are actually paid are controlled by the closed-interval gradient inequality.
-- source:
--   Smooth Gaussian finite-cap subcase of Avram, Palmowski and Pistorius (2007), Proposition 4(i), Section 5.4 and (5.13), https://arxiv.org/pdf/math/0702893#page=19. Auxiliary to Prove2Me theorem d6e4d464-0ce5-506d-83e4-ea1b40d7596a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.gaussian_finitecap_diagonal_cash_bound_of_contDiffOn_closed_cap_neighborhood
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (hc : 0 < X.c)
    (q : ℝ) (hq : 0 < q) (v : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (a b : ℝ) (ha : a < 0) (hb : C.toReal < b)
    (hvSmooth : ContDiffOn ℝ 2 v (Ioo a b))
    (hvNonneg : ∀ y ∈ Icc (0 : ℝ) C.toReal, 0 ≤ v y)
    (hvGen : ∀ y ∈ Icc (0 : ℝ) C.toReal, X.generator v y - q * v y ≤ 0)
    (hvGrad : ∀ y ∈ Icc (0 : ℝ) C.toReal, 1 ≤ deriv v y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (v x) := by sorry
