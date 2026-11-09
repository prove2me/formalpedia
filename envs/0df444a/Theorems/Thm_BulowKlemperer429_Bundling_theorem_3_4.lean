-- Prove2me | Theorems.Thm_BulowKlemperer429_Bundling_theorem_3_4
-- name    : BulowKlemperer429.Bundling.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:45:07.518744+00:00
-- url     : https://prove2.me/theorems/81ff174f-b836-4320-9933-e7daa5f38b4e
-- title:
--   Theorem 3.4 — atomless regular two-item tightness
-- statement:
--   For every $\varepsilon>0$, there exist two independent nonnegative item values whose marginal laws are atomless and regular. Their product law $D$ satisfies $\mathrm{BREV}(D)>0$ and
--   $$\mathrm{REV}(D)\ge(2-\varepsilon)\mathrm{BREV}(D).$$
--   The existential witnesses are not fixed in the statement. This supplies the lower bound in Theorem 1.1 and rules out any smaller uniform factor in the comparison with bundle posted pricing.
--
--   **Formalization Note** Atomlessness means every singleton has measure zero. For $\varepsilon\ge2$ the lower bound is automatic, but existence, regularity, atomlessness and positive bundle revenue remain required.
--
--   Differences from the source:
--   - generalization: nonnegative-price mechanisms with expected payment → the published Rev supremum also allows negative payments and extended expected revenue, requiring payment measurability only; reason: every source mechanism is included; IC bounds negative payments below by the payment at zero, and adding u(0) normalizes payments to be nonnegative and weakly increases them, so the optimal benchmark agrees
--   - encoding: closed truthful individually rational menus → feasible IC and IR direct mechanisms on the entire nonnegative orthant with measurable payment; reason: the direct mechanism records the selected option at every type; lotteries are allowed and no allocation measurability is imposed
--   - encoding: finite monopoly revenue assumed throughout → no separate finite-revenue hypothesis for regular marginals; reason: the nonnegative concave revenue curve is bounded on (0,1), which implies finite posted-price revenue
--   - encoding: (2−ε) BREV in a real inequality → ENNReal.ofReal (2 - ε) times BREV; reason: BREV is finite and nonnegative for these regular laws, so clipping a nonpositive coefficient to zero changes no instance
-- source:
--   Yichen Huang, STOC 2027 submission #429 (October 2026), p. 10, Theorem 3.4 (PDF p. 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/429.pdf

import Mathlib
import Definitions.Def_BulowKlemperer429_Bundling_Revenue
import Definitions.Def_MultiItemRev_BundlingOpt_Model
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace BulowKlemperer429.Bundling

theorem theorem_3_4 :
    ∀ ε : ℝ, 0 < ε → ∃ ν : Fin 2 → Measure ℝ≥0,
      (∀ j, IsProbabilityMeasure (ν j)) ∧ (∀ j, NullSingletonClass (ν j)) ∧
      (∀ j, IsRegular (ν j)) ∧ 0 < BREV ν ∧
      ENNReal.ofReal (2 - ε) * BREV ν ≤ MultiItemRev.BundlingOpt.Rev (Measure.pi ν) := by sorry

end BulowKlemperer429.Bundling
