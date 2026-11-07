-- Prove2me | Theorems.Thm_AdaptiveSparsify_lemma_4_13
-- name    : AdaptiveSparsify.lemma_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:47:30.732269+00:00
-- url     : https://prove2.me/theorems/a7345113-27b0-4222-9ad0-5aa6b288827c
-- title:
--   Lemma 4.13 — the feasibility error after a step is at most $\alpha^2$ with high probability
-- statement:
--   Let $(x,s)$ be $\varepsilon$ well-centered at $t$, and take a step of Algorithm 1 with valid inputs and $R$ drawn as in Lemma 6.3. Then with high probability $x^{\mathrm{new}}$ lies in the barrier domain and
--
--   $$\|A^\top x^{\mathrm{new}}-b\|_{(A^\top\nabla^2\Phi(x^{\mathrm{new}})^{-1}A)^{-1}}\le\alpha^2.$$
--
--   The feasibility error thus shrinks quadratically in each step, which is how a sampled step keeps $A^\top x$ close to $b$.
--
--   Differences from the source:
--   - reading: "sufficiently small" ε, large C_center, C_var and sample constant, C_K absolute → explicit quantifiers: C_K, then ε₀, then ε, then the other constants in the order of the proof, all before the instance; reason: p.17 and §6.4 hide these constants; they may depend on C_K, which is an absolute constant (reading R1)
--   - reading: §4 assumes n large enough for log n > 0 → n ≥ 2; reason: λ = C_center log n / ε² vanishes at n = 1 and α is then undefined
--   - reading: "with high probability" → failure at most n^{−c} for every c > 0, with the sampling constant chosen after c; reason: Lemma 6.3 scales the failure exponent with its constant
--   - reading: the conclusion mentions ∇²Φ(x^new) only → x^new is also required to lie in the barrier domain; reason: the norm at x^new means nothing outside the domain, and the proof obtains membership from Lemma 4.12
--   - reading: "Assume that (x, s) are ε well-centered" → also an admissible instance and valid x̄, s̄, H, τ̃, with R drawn by Lemma 6.3 for K′ samples; reason: Algorithm 1 is the setting of the lemma
-- source:
--   Liu, Peng, Tang, Weng, Yang, Adaptive Matrix Sparsification with Applications to Empirical Risk Minimization and Computational Geometry (manuscript, sha256 7a66a27b…), Lemma 4.13, p.27

import Mathlib
import Definitions.Def_AdaptiveSparsify_IPM

open Matrix

namespace AdaptiveSparsify

/-- **Lemma 4.13** (Feasibility analysis), p.27.

Liu, Peng, Tang, Weng, Yang, *Adaptive Matrix Sparsification …* (manuscript, sha256 7a66a27b…), Lemma 4.13, p.27.

"Assume that (x, s) are ε well-centered at path parameter t. Then with high probability,
‖A⊤x^new − b‖_{(A⊤∇²Φ(x^new)⁻¹A)⁻¹} ≤ α²."

**Formalization Note.** "With high probability" is failure at most `n^{-c}`, for every `c`, with the
sampling constant chosen after `c`, for `R` drawn as in Lemma 6.3. The event also requires `x^new` in the
barrier domain, without which the norm at `x^new` has no meaning; the proof obtains this from Lemma 4.12. -/
theorem lemma_4_13 : ∀ CK : ℕ, 1 ≤ CK → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 80 ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ Cc₀ : ℝ, 0 < Cc₀ ∧ ∀ Cc : ℝ, Cc₀ ≤ Cc →
      ∀ c : ℝ, 0 < c → ∃ Cs₀ : ℝ, 0 < Cs₀ ∧ ∀ Cs : ℝ, Cs₀ ≤ Cs →
        ∀ I : ERMInstance, I.IsAdmissible CK → 2 ≤ I.blocks.n →
        ∀ (t : ℝ) (x s : Fin I.blocks.n → ℝ) (ch : I.StepChoice), 0 < t →
          let p : Params := ⟨CK, ε, Cc⟩
          I.WellCentered (p.alpha I.blocks.n) ε t x s → ch.Valid p t x s →
          probOf (sampleWeight (K' := ch.stepCount p Cs) (ch.stepP p t x))
            (fun idx => ¬ ERMInstance.FeasibleStep p (ch.xAt p Cs t x idx)) ≤
            (I.blocks.n : ℝ) ^ (-c) := by sorry

end AdaptiveSparsify
