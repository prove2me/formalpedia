-- Prove2me | Theorems.Thm_BartlettNN_Sigmoid_theorem28_part1
-- name    : BartlettNN.Sigmoid.theorem28_part1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T01:15:51.788743+00:00
-- url     : https://prove2.me/theorems/2d0c27b3-3aa2-48bb-bb0e-5ac7c90fe837
-- title:
--   Theorem 28(1) — bounded-weight sigmoid networks generalize
-- statement:
--   Let $\sigma:\mathbb R\to[-1,1]$ be nondecreasing. Let $F$ be all functions $x\mapsto\sigma(w\cdot x+w_0)$ on $\mathbb R^n$, and let $H=\operatorname{combos}(F,A)$ for $A\ge1$. For a probability distribution $P$ on $\mathbb R^n\times\{-1,1\}$, $0<\gamma\le1$, $0<\delta<1/2$, and an independent sample of length $m\ge1$, one universal positive constant $c$, chosen before every model and sample parameter, gives with probability at least $1-\delta$ simultaneously for all $h\in H$:
--
--   $$\operatorname{er}_P(h)<\widehat{\operatorname{er}}_z^\gamma(h)+\sqrt{\frac cm\left[\frac{A^2n}{\gamma^2}\log\!\left(\frac{32A}{\gamma}\right)(\log m)^2+\log\!\left(\frac1\delta\right)\right]}.$$
--
--   The bound depends on the sum of absolute output weights and input dimension, with no fixed number of hidden units. **Correction:** the paper prints $\log(A/\gamma)$; its proof supplies $\log(32A/\gamma)$, which stays positive at $A=\gamma=1$. The only measurability assumption left explicit is that the event of a violating network is measurable, as the paper assumes for all sets considered.
-- source:
--   Bartlett, The Sample Complexity of Pattern Classification with Neural Networks, IEEE Trans. Inform. Theory 44 (1998), p. 534, Theorem 28(1), using Corollary 24 p. 533; https://doi.org/10.1109/18.661502

import Mathlib
import Definitions.Def_BartlettNN_Sigmoid_Classification
import Definitions.Def_BartlettNN_Sigmoid_Networks

open MeasureTheory

namespace BartlettNN.Sigmoid

/-- Theorem 28(1), p. 534, with the positive logarithm `log(32A/γ)` supplied by Corollary 24. -/
theorem theorem28_part1 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ) (σ : ℝ → ℝ)
        (P : Measure ((Fin n → ℝ) × Bool)) (_ : IsProbabilityMeasure P)
        (γ δ A : ℝ) (m : ℕ),
        Monotone σ → (∀ t, σ t ∈ Set.Icc (-1 : ℝ) 1) →
        0 < γ → γ ≤ 1 → 0 < δ → δ < 1 / 2 → 1 ≤ A → 1 ≤ m →
        MeasurableSet {z : Fin m → (Fin n → ℝ) × Bool |
          ∃ h ∈ BartlettNN.FatNet.combos (sigmoidUnits σ n) A,
            BartlettNN.Margin.erHat γ z h + Real.sqrt ((c / m) *
              ((A ^ 2 * n / γ ^ 2) * Real.log (32 * A / γ) * (Real.log m) ^ 2 +
                Real.log (1 / δ))) ≤ BartlettNN.Margin.er P h} →
        (Measure.pi fun _ : Fin m => P) {z |
          ∃ h ∈ BartlettNN.FatNet.combos (sigmoidUnits σ n) A,
            BartlettNN.Margin.erHat γ z h + Real.sqrt ((c / m) *
              ((A ^ 2 * n / γ ^ 2) * Real.log (32 * A / γ) * (Real.log m) ^ 2 +
                Real.log (1 / δ))) ≤ BartlettNN.Margin.er P h} ≤ ENNReal.ofReal δ := by sorry

end BartlettNN.Sigmoid
