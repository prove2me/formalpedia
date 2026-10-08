-- Prove2me | Theorems.Thm_BartlettNN_Sigmoid_corollary24_sigmoid_fat
-- name    : BartlettNN.Sigmoid.corollary24_sigmoid_fat
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T01:39:25.047239+00:00
-- url     : https://prove2.me/theorems/92ea02be-6b7a-4e9a-939a-dca678bc336f
-- title:
--   Corollary 24 — fat dimension of bounded-weight sigmoid networks
-- statement:
--   Let $\sigma:\mathbb R\to[-M/2,M/2]$ be nondecreasing, $M>0$, and let $F$ contain every affine-input $\sigma$ unit on $\mathbb R^n$. Set $H=\operatorname{combos}(F,A)$. A single positive constant $c$, independent of all choices of $n,\sigma,M,A,\gamma$, satisfies, for $n\ge1$, $A\ge1$ and $0<\gamma\le MA$,
--
--   $$\operatorname{fat}_H(\gamma)\le\frac{cM^2A^2n}{\gamma^2}\log\!\left(\frac{MA}{\gamma}\right)<\infty.$$
--
--   This is the weight-based capacity bound for two-layer networks with arbitrarily many units. **Correction:** positive margin and $n\ge1$ are explicit; the printed formula is false at $n=0$ because the network still has its bias.
-- source:
--   Bartlett, The Sample Complexity of Pattern Classification with Neural Networks, IEEE Trans. Inform. Theory 44 (1998), p. 533, Corollary 24; https://doi.org/10.1109/18.661502

import Mathlib
import Definitions.Def_BartlettNN_Sigmoid_Fat
import Definitions.Def_BartlettNN_Sigmoid_Networks

namespace BartlettNN.Sigmoid

/-- Corollary 24, p. 533, with positive margin and positive input dimension. -/
theorem corollary24_sigmoid_fat :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ) (σ : ℝ → ℝ) (M A γ : ℝ),
        1 ≤ n → Monotone σ →
        (∀ t, σ t ∈ Set.Icc (-M / 2) (M / 2)) →
        0 < M → 1 ≤ A → 0 < γ → γ ≤ M * A →
        ∃ d : ℕ, BartlettNN.Margin.fat (BartlettNN.FatNet.combos (sigmoidUnits σ n) A) γ = d ∧
          (d : ℝ) ≤ (c * M ^ 2 * A ^ 2 * n / γ ^ 2) * Real.log (M * A / γ) := by sorry

end BartlettNN.Sigmoid
