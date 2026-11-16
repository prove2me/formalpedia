-- Prove2me | Theorems.Thm_BulowKlemperer429_Bundling_Supplement_theorem_1_2
-- name    : BulowKlemperer429.Bundling.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:39:54.84301+00:00
-- url     : https://prove2.me/theorems/4e5dabee-7fcb-44aa-ad7f-6375193c2059
-- title:
--   Theorem 1.2 — $\mathrm{REV}\le\mathrm{SREV}+\frac{\pi^2}{6}\mathrm{BREV}\le(1+\frac{\pi^2}{6})\max\{\mathrm{SREV},\mathrm{BREV}\}$
-- statement:
--   For one additive bidder with independent nonnegative item values (finitely many items), let $D$ be the product law, $\mathrm{REV}(D)$ the optimal truthful revenue, $\mathrm{SREV}(D)=\sum_j\sup_{t\ge0}t\Pr[V_j\ge t]$ the separate-selling revenue and $\mathrm{BREV}(D)=\sup_{t\ge0}t\Pr[S\ge t]$ the grand-bundling revenue, $S=\sum_jV_j$. Then for every product distribution $D$,
--   $$\mathrm{REV}(D)\le\mathrm{SREV}(D)+\frac{\pi^2}{6}\mathrm{BREV}(D)\le\Big(1+\frac{\pi^2}{6}\Big)\max\{\mathrm{SREV}(D),\mathrm{BREV}(D)\}.$$
--
--   Both inequalities are asserted. The factor $1+\pi^2/6<2.645$ improves the earlier factors $6$ and $5.2$ for the better of separate selling and grand bundling.
--
--   **Formalization Note** Revenues are extended nonnegative reals; $\mathrm{SREV}$ and $\mathrm{BREV}$ are posted-price suprema with the weak sale inequality.
--
--   Differences from the source:
--   - generalization: nonnegative-price mechanisms with expected payment → the published Rev supremum also allows negative payments and extended expected revenue, requiring payment measurability only; reason: every source mechanism is included; IC bounds negative payments below by the payment at zero, and adding u(0) normalizes payments to be nonnegative and weakly increases them, so the optimal benchmark agrees
--   - encoding: closed truthful individually rational menus → feasible IC and IR direct mechanisms on the entire nonnegative orthant with measurable payment; reason: the direct mechanism records the selected option at every type; lotteries are allowed and no allocation measurability is imposed
--   - encoding: values and revenues written as nonnegative real quantities, with expectations possibly infinite → NNReal values and ENNReal revenue suprema and nonnegative integrals; reason: the representation includes unbounded laws with infinite mean and avoids the zero default of a nonintegrable Bochner integral
--   - generalization: throughout, each marginal has finite monopoly revenue (p. 1, p. 6) → no finite-revenue hypothesis; reason: if some marginal has infinite posted-price revenue then SREV = ∞ and the right side is ∞, so the inequality is trivial; on finite-revenue marginals the statement is the source's
--   - encoding: coefficients π²/6 and 1 + π²/6 → ENNReal.ofReal(π²/6) and ENNReal.ofReal(1 + π²/6); reason: both coefficients are positive reals, so the coercion is exact
-- source:
--   Yichen Huang, STOC 2027 submission #429 (October 2026), p. 2, Theorem 1.2; proof via Theorem 4.3, Lemma 4.4 and Corollary 4.5, p. 15 (PDF p. 16) (PDF p. 3); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/429.pdf

import Mathlib
import Definitions.Def_BulowKlemperer429_Bundling_Revenue
import Definitions.Def_MultiItemRev_BundlingOpt_Model
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace BulowKlemperer429.Bundling.Supplement

theorem theorem_1_2 :
    ∀ (ι : Type) [Fintype ι] (ν : ι → Measure ℝ≥0),
      (∀ j, IsProbabilityMeasure (ν j)) →
      MultiItemRev.BundlingOpt.Rev (Measure.pi ν) ≤
          SREV ν + ENNReal.ofReal (Real.pi ^ 2 / 6) * BREV ν ∧
        SREV ν + ENNReal.ofReal (Real.pi ^ 2 / 6) * BREV ν ≤
          ENNReal.ofReal (1 + Real.pi ^ 2 / 6) * max (SREV ν) (BREV ν) := by sorry


end BulowKlemperer429.Bundling.Supplement
