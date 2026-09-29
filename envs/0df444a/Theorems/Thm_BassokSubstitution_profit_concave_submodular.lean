-- Prove2me | Theorems.Thm_BassokSubstitution_profit_concave_submodular
-- name    : BassokSubstitution.profit_concave_submodular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T08:23:48.685971+00:00
-- url     : https://prove2.me/theorems/cb8ed534-f974-4c17-aee1-fcb60f127ecb
-- title:
--   Proposition 2 — the expected profit $P(x,y)$ is concave and submodular in $y$
-- statement:
--   Consider the model with Assumptions 1–3 and $b \ge 0$, and independent nonnegative demands $D_1,\dots,D_N$ with finite means and densities, with joint law $F = \nu_1\otimes\dots\otimes\nu_N$. Fix a starting inventory $x \in \mathbb R^N$. Then the expected profit $y \mapsto P(x,y)$ is concave on the nonnegative orthant $\{y \ge 0\}$, and it is submodular there: for all $y, y' \ge 0$,
--   $$P(x, y \vee y') + P(x, y \wedge y') \le P(x, y) + P(x, y'),$$
--   where $\vee$ and $\wedge$ are the componentwise maximum and minimum.
--
--   Concavity lets the optimal ordering decision be characterized by first-order conditions; submodularity (the products are substitutes) drives the comparison of the partial derivatives in the proof of Theorem 2.
--
--   **Formalization Note.** The paper defines submodularity for twice differentiable functions by nonpositive cross partials (Definition 2, Appendix A). The lattice inequality above is used instead; for $C^2$ functions on a box the two are equivalent, and the lattice form needs no second derivatives. Independence, finite means and densities are the paper's unstated standing hypotheses (see the Profit definition).
-- source:
--   Bassok, Anupindi, Akella, Single-Period Multiproduct Inventory Models with Substitution, Operations Research 47(4):632–642 (1999), p. 634, Proposition 2 (proof in Appendix B, pp. 639–641; submodularity as in Definition 2, p. 638)

import Mathlib
import Definitions.Def_BassokSubstitution_Profit

open MeasureTheory

namespace BassokSubstitution

/-- Proposition 2: the expected profit `y ↦ P(x, y)` is concave and (lattice-)submodular on
the nonnegative orthant. -/
theorem profit_concave_submodular {N : ℕ} (M : Model N)
    (hA1 : M.Assumption1) (hA2 : M.Assumption2) (hA3 : M.Assumption3) (hb : 0 ≤ M.b)
    (ν : Fin N → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] (hν : DemandLaw ν)
    (x : Fin N → ℝ) :
    ConcaveOn ℝ {y : Fin N → ℝ | 0 ≤ y} (M.profit (Measure.pi ν) x) ∧
      ∀ y y' : Fin N → ℝ, 0 ≤ y → 0 ≤ y' →
        M.profit (Measure.pi ν) x (y ⊔ y') + M.profit (Measure.pi ν) x (y ⊓ y') ≤
          M.profit (Measure.pi ν) x y + M.profit (Measure.pi ν) x y' := by sorry

end BassokSubstitution
