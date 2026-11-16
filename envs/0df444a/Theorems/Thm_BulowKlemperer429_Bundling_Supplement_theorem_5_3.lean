-- Prove2me | Theorems.Thm_BulowKlemperer429_Bundling_Supplement_theorem_5_3
-- name    : BulowKlemperer429.Bundling.Supplement.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:41:11.550204+00:00
-- url     : https://prove2.me/theorems/75a77495-54c0-407d-a2c4-c2f90a788122
-- title:
--   Theorem 5.3 — three bundle prices earn more than $(2.02-\varepsilon)\max\{\mathrm{SREV},\mathrm{BREV}\}$
-- statement:
--   For every $\varepsilon>0$ there is a finite product distribution $D$ of independent nonnegative item values, each with finite monopoly revenue, together with three nonempty pairwise-disjoint bundles $B_1,B_2,B_3$ of items and prices $p_1,p_2,p_3\ge0$, such that the posted-price revenue
--   $$\sum_{i=1}^3p_i\Pr\Big[\sum_{j\in B_i}V_j\ge p_i\Big]>(2.02-\varepsilon)\max\{\mathrm{SREV}(D),\mathrm{BREV}(D)\}.$$
--
--   The left side is what one additive bidder pays when each bundle is offered at its own price; it lower-bounds $\mathrm{REV}(D)$, so the factor $2$ is not achievable by the better of separate selling and grand bundling.
--
--   **Formalization Note** The coefficient is the nonnegative real $\max(2.02-\varepsilon,0)$; for $\varepsilon\ge2.02$ the Lean statement still asks for positive bundle revenue. Bundles need not cover all items.
--
--   Differences from the source:
--   - encoding: a finite product distribution D → m : ℕ and independent item laws ν : Fin m → Measure ℝ≥0, each a probability measure, D = Measure.pi ν; reason: finitely many independent nonnegative item values, exactly the model of §2
--   - encoding: throughout, each marginal has finite monopoly revenue (p. 1, p. 6) → the witness satisfies postedRevenue (ν j) < ⊤ for every item, as a conjunct; reason: the standing model assumption becomes part of what the constructed distribution must satisfy
--   - encoding: posted prices for three disjoint bundles earn … → bundlePriceRevenue ν B p = Σ_i p_i · Pr[Σ_{j∈B_i} V_j ≥ p_i] for three nonempty pairwise-disjoint finite sets B_i of items and prices p_i ≥ 0; reason: for an additive bidder and disjoint bundles the purchase decisions separate ("Offers on disjoint groups form a truthful menu", p. 17); the weak inequality is the paper's posted-price convention REV(X) = sup_t t Pr[X ≥ t] (p. 6)
--   - generalization: (2.02 − ε) max{SREV, BREV} < revenue, a real inequality → ENNReal.ofReal(202/100 − ε) · max{SREV, BREV} < bundlePriceRevenue; reason: for ε < 2.02 the two agree because max{SREV, BREV} is finite; for ε ≥ 2.02 the printed claim is automatic while the Lean claim still asks for positive bundle revenue, a stronger conclusion that specializes to the printed one
-- source:
--   Yichen Huang, STOC 2027 submission #429 (October 2026), p. 17, Theorem 5.3 (PDF p. 18); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/429.pdf

import Mathlib
import Definitions.Def_BulowKlemperer429_Bundling_Supplement_Benchmarks
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace BulowKlemperer429.Bundling.Supplement

theorem theorem_5_3 :
    ∀ ε : ℝ, 0 < ε → ∃ (m : ℕ) (ν : Fin m → Measure ℝ≥0),
      (∀ j, IsProbabilityMeasure (ν j)) ∧ (∀ j, postedRevenue (ν j) < ⊤) ∧
      ∃ (B : Fin 3 → Finset (Fin m)) (p : Fin 3 → ℝ≥0),
        (∀ i, (B i).Nonempty) ∧ Pairwise (fun i i' => Disjoint (B i) (B i')) ∧
        ENNReal.ofReal (202 / 100 - ε) * max (SREV ν) (BREV ν) < bundlePriceRevenue ν B p := by sorry


end BulowKlemperer429.Bundling.Supplement
