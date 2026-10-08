-- Prove2me | Theorems.Thm_BartlettNN_Sigmoid_theorem2_margin_bound
-- name    : BartlettNN.Sigmoid.theorem2_margin_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T01:39:15.449278+00:00
-- url     : https://prove2.me/theorems/0b82a154-87fc-46c1-b1da-9f342a132362
-- title:
--   Theorem 2 — uniform fat-shattering margin bound
-- statement:
--   Let $H$ be a class of measurable real-valued scores on $X$, let $P$ be a probability distribution on $X\times\{-1,1\}$, and draw $m\ge1$ examples independently. Assume $0<\gamma<1$, $0<\delta<1/2$, and $d=\operatorname{fat}_H(\gamma/16)\le34m$. Then, with probability at least $1-\delta$, every $h\in H$ satisfies
--
--   $$\operatorname{er}_P(h)<\widehat{\operatorname{er}}_z^\gamma(h)+\sqrt{\frac2m\left[d\ln\!\left(\frac{34em}{d}\right)\log_2(578m)+\ln\!\left(\frac4\delta\right)\right]}.$$
--
--   At $d=0$ the product $d\ln(C/d)$ takes its continuous value zero. The statement is uniform over $H$ and requires the paper's measurable bad event and its double-sample event (1) at every threshold, following the paper's standing assumption that all sets considered are measurable. **Correction:** $d\le34m$ excludes the range where the printed logarithmic term would cease to be a valid bound.
-- source:
--   Bartlett, The Sample Complexity of Pattern Classification with Neural Networks, IEEE Trans. Inform. Theory 44 (1998), p. 527, Theorem 2; https://doi.org/10.1109/18.661502

import Mathlib
import Definitions.Def_BartlettNN_Sigmoid_Classification
import Definitions.Def_BartlettNN_Sigmoid_Fat

open MeasureTheory

namespace BartlettNN.Sigmoid

/-- Theorem 2, p. 527, with the high-dimension range of its printed logarithm excluded. -/
theorem theorem2_margin_bound :
    ∀ {X : Type} [MeasurableSpace X] (H : Set (X → ℝ))
      (P : Measure (X × Bool)) (_ : IsProbabilityMeasure P)
      (γ δ : ℝ) (m d : ℕ),
      0 < γ → γ < 1 → 0 < δ → δ < 1 / 2 → 1 ≤ m →
      BartlettNN.Margin.fat H (γ / 16) = d → (d : ℝ) ≤ 34 * m →
      (∀ h ∈ H, Measurable h) →
      (∀ ε : ℝ, MeasurableSet (doubleSampleEvent H γ ε m)) →
      MeasurableSet {z : Fin m → X × Bool | ∃ h ∈ H,
        BartlettNN.Margin.erHat γ z h + Real.sqrt ((2 / (m : ℝ)) *
          ((d : ℝ) * Real.log (34 * Real.exp 1 * m / d) * Real.logb 2 (578 * m) +
            Real.log (4 / δ))) ≤ BartlettNN.Margin.er P h} →
      (Measure.pi fun _ : Fin m => P) {z | ∃ h ∈ H,
        BartlettNN.Margin.erHat γ z h + Real.sqrt ((2 / (m : ℝ)) *
          ((d : ℝ) * Real.log (34 * Real.exp 1 * m / d) * Real.logb 2 (578 * m) +
            Real.log (4 / δ))) ≤ BartlettNN.Margin.er P h} ≤ ENNReal.ofReal δ := by sorry

end BartlettNN.Sigmoid
