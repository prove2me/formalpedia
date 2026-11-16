-- Prove2me | Theorems.Thm_BulowKlemperer429_Bundling_Supplement_theorem_4_3
-- name    : BulowKlemperer429.Bundling.Supplement.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:38:49.575361+00:00
-- url     : https://prove2.me/theorems/3b5f5210-593d-43f7-a375-c24e8c1b8659
-- title:
--   Theorem 4.3 — $\mathrm{REV}(D)\le J(S)+\mathrm{SREV}(D)$
-- statement:
--   Consider one additive bidder with independent nonnegative item values $V_j\sim F_j$, $j$ in a finite set, product law $D$ and total value $S=\sum_jV_j$. Put $\varphi(q)=q+(1-q)\log(1-q)$ for $0\le q\le 1$, with $\varphi(1)=1$, and define the tail statistic
--   $$J(X)=\int_0^\infty\varphi\big(\Pr[X>t]\big)\,dt\in[0,\infty].$$
--   Let $\mathrm{REV}(D)$ be the optimal revenue over truthful individually rational mechanisms, including lotteries, and $\mathrm{SREV}(D)=\sum_j\sup_{t\ge0}t\Pr[V_j\ge t]$ the separate-selling revenue. Then for every product distribution $D$,
--   $$\mathrm{REV}(D)\le J(S)+\mathrm{SREV}(D).$$
--
--   This is the entropy comparison behind Theorem 1.2: with Lemma 4.4 applied to $S$ it gives $\mathrm{REV}\le\mathrm{SREV}+(\pi^2/6)\mathrm{BREV}$.
--
--   **Formalization Note** Every finite index type is allowed, including a single item; no boundedness, regularity or finite support is assumed. $J$ and all revenues are extended nonnegative reals; $J$ is the paper's tail-integral definition, which applies to unbounded $S$.
--
--   Differences from the source:
--   - generalization: nonnegative-price mechanisms with expected payment → the published Rev supremum also allows negative payments and extended expected revenue, requiring payment measurability only; reason: every source mechanism is included; IC bounds negative payments below by the payment at zero, and adding u(0) normalizes payments to be nonnegative and weakly increases them, so the optimal benchmark agrees
--   - encoding: closed truthful individually rational menus → feasible IC and IR direct mechanisms on the entire nonnegative orthant with measurable payment; reason: the direct mechanism records the selected option at every type; lotteries are allowed and no allocation measurability is imposed
--   - encoding: values and revenues written as nonnegative real quantities, with expectations possibly infinite → NNReal values and ENNReal revenue suprema and nonnegative integrals; reason: the representation includes unbounded laws with infinite mean and avoids the zero default of a nonintegrable Bochner integral
--   - generalization: throughout, each marginal has finite monopoly revenue (p. 1, p. 6) → no finite-revenue hypothesis; reason: if some marginal has infinite posted-price revenue then SREV = ∞ and the right side is ∞, so the inequality is trivial; on finite-revenue marginals the statement is the source's
--   - encoding: J(S) for unbounded S defined by ∫_0^∞ φ(Pr[S > t]) dt → tailJ of the bundle law, a [0,∞]-valued lintegral of ENNReal.ofReal(φ(Pr[S > t])) over t > 0, with φ(1) = 1 from Real.log 0 = 0; reason: φ is nonnegative on [0,1], so this is the paper's integral; the value may be infinite
-- source:
--   Yichen Huang, STOC 2027 submission #429 (October 2026), p. 14, Theorem 4.3 (PDF p. 15); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/429.pdf

import Mathlib
import Definitions.Def_BulowKlemperer429_Bundling_Supplement_Entropy
import Definitions.Def_BulowKlemperer429_Bundling_Revenue
import Definitions.Def_MultiItemRev_BundlingOpt_Model
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace BulowKlemperer429.Bundling.Supplement

theorem theorem_4_3 :
    ∀ (ι : Type) [Fintype ι] (ν : ι → Measure ℝ≥0),
      (∀ j, IsProbabilityMeasure (ν j)) →
      MultiItemRev.BundlingOpt.Rev (Measure.pi ν) ≤ tailJ (bundleLaw ν) + SREV ν := by sorry


end BulowKlemperer429.Bundling.Supplement
