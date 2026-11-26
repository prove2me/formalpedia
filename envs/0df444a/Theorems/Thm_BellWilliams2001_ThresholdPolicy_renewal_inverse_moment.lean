-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_renewal_inverse_moment
-- name    : BellWilliams2001.ThresholdPolicy.renewal_inverse_moment
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T05:45:33.126951+00:00
-- url     : https://prove2.me/theorems/8117d7bb-8aa3-5d75-a3b8-d8f3fa37d98d
-- title:
--   Polynomial maximal moment bound for a centered renewal count
-- statement:
--   For independent identically distributed strictly positive interrenewal times of mean one, suppose the centered duration has a finite $p$-th absolute moment, with $p\ge2$. On every interval $[0,R]$, the supremum of $|N(t)-t|^p$ has a measurable majorant whose expectation is at most $C(1+R)^{p/2}$ for some constant $C$ independent of $R$. Here $N(t)$ is the renewal count.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343, Section 9, general form of the centered renewal estimate used in (164)–(172)

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal

namespace BellWilliams2001.ThresholdPolicy

theorem renewal_inverse_moment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i))
    (hpos : ∀ i ω, 0 < U i ω) (hI : iIndepFun U P)
    (hid : ∀ i, IdentDistrib (U i) (U 0) P P)
    (hfin : ∀ ω, Tendsto (fun j => ∑ i ∈ range j, U i ω) atTop atTop)
    (hint : ∀ i, Integrable (U i) P) (hmean : ∀ i, ∫ ω, U i ω ∂P = 1)
    (p : ℝ) (hp : 2 ≤ p) (hpfin : (∫⁻ ω, ENNReal.ofReal |U 0 ω - 1|^p ∂P) < ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r →
      ∃ J : Ω → ℝ≥0∞, Measurable J ∧
        (∀ ω, (⨆ s ∈ Set.Icc 0 r, ENNReal.ofReal
          |(((renewalCount (fun j => ∑ i ∈ range j, U i ω) s).toNat : ℕ) : ℝ) - s|^p) ≤ J ω) ∧
        (∫⁻ ω, J ω ∂P) ≤ ENNReal.ofReal (C * (1+r)^(p/2)) := by sorry

end BellWilliams2001.ThresholdPolicy
