-- Prove2me | Theorems.Thm_BulowKlemperer429_Bundling_display_1
-- name    : BulowKlemperer429.Bundling.display_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:45:57.284553+00:00
-- url     : https://prove2.me/theorems/a7c10325-0de6-4282-865a-ed7d4124bf89
-- title:
--   Display (1) — unallocated value covers residual variation
-- statement:
--   Let $V$ have finitely many independent nonnegative regular coordinates. Let $M$ be a feasible truthful individually rational mechanism with measurable payment and nonnegative prices, and suppose its residual $w(v)$ is bounded above on the entire nonnegative orthant. Then
--   $$G(w(V))\le\mathbb E[\ell(V)].$$
--   This is the key residual comparison displayed as (1). The bound is on the residual, not on the item values or their supports.
--
--   **Formalization Note** No measurable-allocation hypothesis is imposed. Truthfulness and feasibility make $w$ continuous; $\ell=w-p$ is measurable and $0\le\ell\le w$. The bound on $w$ therefore makes both observables integrable.
--
--   Differences from the source:
--   - encoding: closed truthful individually rational menus → feasible IC and IR direct mechanisms on the entire nonnegative orthant with measurable payment; reason: the direct mechanism records the selected option at every type; lotteries are allowed and no allocation measurability is imposed
--   - encoding: finite monopoly revenue assumed throughout → no separate finite-revenue hypothesis for regular marginals; reason: the nonnegative concave revenue curve is bounded on (0,1), which implies finite posted-price revenue
-- source:
--   Yichen Huang, STOC 2027 submission #429 (October 2026), p. 8, Display (1), with §3.1 preamble p. 7 (PDF p. 8) (PDF p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/429.pdf

import Mathlib
import Definitions.Def_BulowKlemperer429_Bundling_Revenue
import Definitions.Def_BulowKlemperer429_Bundling_Residual
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace BulowKlemperer429.Bundling

theorem display_1 {ι : Type} [Fintype ι]
    (ν : ι → Measure ℝ≥0) [∀ j, IsProbabilityMeasure (ν j)]
    (hreg : ∀ j, IsRegular (ν j))
    (M : MultiItemRev.BundlingOpt.Mechanism ι)
    (hM : MultiItemRev.BundlingOpt.IsAdmissible M)
    (hNPT : MultiItemRev.BundlingOpt.IsNPT M)
    (hbounded : ∃ C : ℝ, ∀ v, residual M v ≤ C) :
    variation (Measure.pi ν) (residual M) ≤
      ∫ v, unallocated M v ∂Measure.pi ν := by sorry

end BulowKlemperer429.Bundling
