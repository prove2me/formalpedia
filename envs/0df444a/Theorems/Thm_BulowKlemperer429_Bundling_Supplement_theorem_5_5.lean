-- Prove2me | Theorems.Thm_BulowKlemperer429_Bundling_Supplement_theorem_5_5
-- name    : BulowKlemperer429.Bundling.Supplement.theorem_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:42:25.495806+00:00
-- url     : https://prove2.me/theorems/a22442c7-d233-4b87-b37e-c82126684f90
-- title:
--   Theorem 5.5 — three bundle prices earn more than $2.11\max\{\mathrm{SREV},\mathrm{BREV}\}$
-- statement:
--   There is a finite product distribution $D$ of independent item values that are nonnegative and bounded (all below a common constant $C$), together with three nonempty pairwise-disjoint bundles $B_1,B_2,B_3$ of items and prices $p_1,p_2,p_3\ge0$, such that
--   $$\sum_{i=1}^3p_i\Pr\Big[\sum_{j\in B_i}V_j\ge p_i\Big]>2.11\,\max\{\mathrm{SREV}(D),\mathrm{BREV}(D)\}.$$
--
--   This is the formal version of Theorem 1.3 (p. 2): together with Theorem 1.2 it places the worst-case ratio of $\mathrm{REV}$ to $\max\{\mathrm{SREV},\mathrm{BREV}\}$ in $[2.11,\,1+\pi^2/6]$.
--
--   **Formalization Note** Boundedness is stated as $\nu_j(\{x>C\})=0$ for every item. Bundles need not cover all items.
--
--   Differences from the source:
--   - encoding: a finite product distribution D → m : ℕ and independent item laws ν : Fin m → Measure ℝ≥0, each a probability measure, D = Measure.pi ν; reason: finitely many independent nonnegative item values, exactly the model of §2
--   - encoding: posted prices for three disjoint bundles earn … → bundlePriceRevenue ν B p = Σ_i p_i · Pr[Σ_{j∈B_i} V_j ≥ p_i] for three nonempty pairwise-disjoint finite sets B_i of items and prices p_i ≥ 0; reason: for an additive bidder and disjoint bundles the purchase decisions separate ("Offers on disjoint groups form a truthful menu", p. 17); the weak inequality is the paper's posted-price convention REV(X) = sup_t t Pr[X ≥ t] (p. 6)
--   - encoding: bounded nonnegative item values → ∃ C : ℝ≥0, every item law gives zero mass to {x > C}; reason: a common bound for finitely many bounded items; nonnegativity is the type ℝ≥0; finite monopoly revenue follows
-- source:
--   Yichen Huang, STOC 2027 submission #429 (October 2026), p. 19, Theorem 5.5; also Theorem 1.3, p. 2 (PDF p. 3) (PDF p. 20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/429.pdf

import Mathlib
import Definitions.Def_BulowKlemperer429_Bundling_Supplement_Benchmarks
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace BulowKlemperer429.Bundling.Supplement

theorem theorem_5_5 :
    ∃ (m : ℕ) (ν : Fin m → Measure ℝ≥0),
      (∀ j, IsProbabilityMeasure (ν j)) ∧ (∃ C : ℝ≥0, ∀ j, ν j {x | C < x} = 0) ∧
      ∃ (B : Fin 3 → Finset (Fin m)) (p : Fin 3 → ℝ≥0),
        (∀ i, (B i).Nonempty) ∧ Pairwise (fun i i' => Disjoint (B i) (B i')) ∧
        ENNReal.ofReal (211 / 100) * max (SREV ν) (BREV ν) < bundlePriceRevenue ν B p := by sorry


end BulowKlemperer429.Bundling.Supplement
