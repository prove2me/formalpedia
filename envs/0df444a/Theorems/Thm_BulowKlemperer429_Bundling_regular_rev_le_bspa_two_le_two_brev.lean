-- Prove2me | Theorems.Thm_BulowKlemperer429_Bundling_regular_rev_le_bspa_two_le_two_brev
-- name    : BulowKlemperer429.Bundling.regular_rev_le_bspa_two_le_two_brev
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:45:02.701216+00:00
-- url     : https://prove2.me/theorems/9546c62b-7e63-45bd-b9c7-908e8886696d
-- title:
--   Theorem 1.1 — REV ≤ BSPA₂ ≤ 2 BREV, with tight factor 2
-- statement:
--   For every finite collection of independent nonnegative item values with regular marginal laws, let $D$ be their product law. Then
--   $$\mathrm{REV}(D)\le\mathrm{BSPA}_2(D)\le2\,\mathrm{BREV}(D).$$
--   The factor $2$ is tight: for every $\varepsilon>0$ there is a two-item product law $D_\varepsilon$ with atomless regular marginals and $\mathrm{BREV}(D_\varepsilon)>0$ such that
--   $$\mathrm{REV}(D_\varepsilon)\ge(2-\varepsilon)\mathrm{BREV}(D_\varepsilon).$$
--   The universal bound allows arbitrary regular marginals, including atoms and infinite-mean laws. The optimum ranges over randomized truthful individually rational mechanisms, and the bundle auction has no reserve. One additional independent bidder suffices for every finite item count; the tightness assertion is a separate conjunct, not an assumption on the universal bound.
--
--   Differences from the source:
--   - generalization: nonnegative-price mechanisms with expected payment → the published Rev supremum also allows negative payments and extended expected revenue, requiring payment measurability only; reason: every source mechanism is included; IC bounds negative payments below by the payment at zero, and adding u(0) normalizes payments to be nonnegative and weakly increases them, so the optimal benchmark agrees
--   - encoding: closed truthful individually rational menus → feasible IC and IR direct mechanisms on the entire nonnegative orthant with measurable payment; reason: the direct mechanism records the selected option at every type; lotteries are allowed and no allocation measurability is imposed
--   - encoding: values and revenues written as nonnegative real quantities, with expectations possibly infinite → NNReal values and ENNReal revenue suprema and nonnegative integrals; reason: the representation includes unbounded laws with infinite mean and avoids the zero default of a nonintegrable Bochner integral
--   - encoding: finite monopoly revenue assumed throughout → no separate finite-revenue hypothesis for regular marginals; reason: the nonnegative concave revenue curve is bounded on (0,1), which implies finite posted-price revenue
--   - encoding: the approximation factor 2 is tight → the full existential statement of Theorem 3.4 is conjoined with the universal inequality chain; reason: the paper introduces Theorem 3.4 as proving the lower bound in Theorem 1.1; the universal part has no witness or menu assumption
--   - encoding: (2−ε) BREV in the tightness clause → ENNReal.ofReal (2 - ε) times BREV; reason: regularity implies finite bundle revenue; for ε ≥ 2 both formulations are automatic while the positive-revenue witness is still required
-- source:
--   Yichen Huang, STOC 2027 submission #429 (October 2026), p. 2, Theorem 1.1; tightness made explicit by Theorem 3.4 p. 10 (PDF p. 11) (PDF p. 3); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/429.pdf

import Mathlib
import Definitions.Def_BulowKlemperer429_Bundling_Revenue
import Definitions.Def_MultiItemRev_BundlingOpt_Model
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace BulowKlemperer429.Bundling

theorem regular_rev_le_bspa_two_le_two_brev :
    (∀ (ι : Type) [Fintype ι] (ν : ι → Measure ℝ≥0),
      (∀ j, IsProbabilityMeasure (ν j)) → (∀ j, IsRegular (ν j)) →
      MultiItemRev.BundlingOpt.Rev (Measure.pi ν) ≤ BSPA 2 ν ∧
        BSPA 2 ν ≤ 2 * BREV ν) ∧
    (∀ ε : ℝ, 0 < ε → ∃ ν : Fin 2 → Measure ℝ≥0,
      (∀ j, IsProbabilityMeasure (ν j)) ∧ (∀ j, NullSingletonClass (ν j)) ∧
      (∀ j, IsRegular (ν j)) ∧ 0 < BREV ν ∧
      ENNReal.ofReal (2 - ε) * BREV ν ≤ MultiItemRev.BundlingOpt.Rev (Measure.pi ν)) := by sorry

end BulowKlemperer429.Bundling
