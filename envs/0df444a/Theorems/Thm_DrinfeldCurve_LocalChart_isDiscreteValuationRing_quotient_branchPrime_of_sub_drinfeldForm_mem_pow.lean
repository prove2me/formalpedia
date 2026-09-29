-- Prove2me | Theorems.Thm_DrinfeldCurve_LocalChart_isDiscreteValuationRing_quotient_branchPrime_of_sub_drinfeldForm_mem_pow
-- name    : DrinfeldCurve.LocalChart.isDiscreteValuationRing_quotient_branchPrime_of_sub_drinfeldForm_mem_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/8417fc68-fa0c-5af8-946e-d73b8b6febc0
-- title:
--   Branch quotients of a Drinfeld chart are discrete valuation rings
-- statement:
--   Let $q$ be a prime number and let $W$ be a discrete valuation ring which is a domain, complete with respect to its maximal ideal (adic completeness), with $\mathfrak m_W = (\pi)$ for an element $\pi \in W$, and of residue characteristic $q$ in the sense that $q \in \mathfrak m_W$. Let $c \in \mathfrak m_W$ be non-zero, and let $f, u, v \in W[[X_0, X_1]]$ be power series in two variables with $u$ and $v$ units, such that $f$ agrees with the Drinfeld form $X_0 X_1^q - X_0^q X_1$ modulo $(X_0, X_1)^{q+2}$. Put $S = W[[X_0,X_1]]/(C(c)\,v - f\,u)$, where $C$ denotes the constant-coefficient inclusion $W \to W[[X_0,X_1]]$. Let $P \subset S$ be a prime ideal such that at least one of the images of $X_0$, $X_1$ in $S$ lies outside $P$, and such that the image of $C(\pi)$ lies in $P$. Then the quotient ring $S/P$ is a discrete valuation ring.
--
--   This is the regularity statement for the individual branches of the Drinfeld local chart of a modular curve at a supersingular point: a prime of the chart ring containing the uniformiser of $W$ but not the whole maximal ideal cuts out a branch whose local ring is a discrete valuation ring. It is used in the analysis of the auxiliary full-level modular curves, where the stalks of the integral two-chart model along components through supersingular points are shown to be discrete valuation rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DrinfeldCurve_LocalChart_isDiscreteValuationRing_quotient_branchPrime_of_sub_drinfeldForm_mem_pow.lean

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem DrinfeldCurve.LocalChart.isDiscreteValuationRing_quotient_branchPrime_of_sub_drinfeldForm_mem_pow
    (q : ℕ) [Fact q.Prime]
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : IsLocalRing.maximalIdeal W = Ideal.span {π})
    (hqW : (q : W) ∈ IsLocalRing.maximalIdeal W)
    (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W) (hc0 : c ≠ 0)
    (f u v : MvPowerSeries (Fin 2) W) (hu : IsUnit u) (hv : IsUnit v)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
    (P : Ideal (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C c * v - f * u})) [P.IsPrime]
    (hPX : Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.X 0) ∉ P ∨
      Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.X 1) ∉ P)
    (hPπ : Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.C π) ∈ P) :
    IsDiscreteValuationRing ((MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C c * v - f * u}) ⧸ P) := by sorry
