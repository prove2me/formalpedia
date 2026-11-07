-- Prove2me | Theorems.Thm_AdaptiveSparsify_lemma_4_11
-- name    : AdaptiveSparsify.lemma_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:47:30.422485+00:00
-- url     : https://prove2.me/theorems/b36450fb-4cf9-40f8-9701-f9e82dd6feac
-- title:
--   Lemma 4.11 — basic step size bounds $\|g\|_2,\|\delta_1\|_2,\|\delta_2\|_2$
-- statement:
--   In a step of Algorithm 1 from a pair $(x,s)$ that is $\varepsilon$ well-centered at $t$, with $0<\varepsilon<1/80$ and valid inputs $\bar x,\bar s,H$:
--
--   1. $\|g\|_2\le\alpha(\varepsilon^2+10\beta\varepsilon)^{1/2}\le1.01\,\alpha\varepsilon$;
--   2. $\|\delta_1\|_2\le C\alpha\varepsilon\exp(\varepsilon)$ for an absolute constant $C$;
--   3. $\|\delta_2\|_2\le\alpha\varepsilon\exp(3\varepsilon/2)$.
--
--   These bounds control all later estimates on the step.
--
--   Differences from the source:
--   - reading: "In Algorithm 1" → (x, s) ε well-centered at t > 0, an admissible instance, and x̄, s̄, H, τ̃ valid for line 2, line 4 and Lemma 6.3; reason: these are the hypotheses the algorithm runs under, and the proof uses them
--   - reading: §4 assumes n large enough for log n > 0 → n ≥ 2; reason: λ = C_center log n / ε² vanishes at n = 1 and α is then undefined
--   - reading: C_center implicit → C_center at least a constant depending on ε and C_K; reason: the proof needs 10βε ≤ 0.02ε² and 3β ≤ ε, which hold for large C_center
--   - reading: ≲ in item 2 → an absolute constant C, chosen first; reason: the meaning of ≲ (p.10)
-- source:
--   Liu, Peng, Tang, Weng, Yang, Adaptive Matrix Sparsification with Applications to Empirical Risk Minimization and Computational Geometry (manuscript, sha256 7a66a27b…), Lemma 4.11, p.25

import Mathlib
import Definitions.Def_AdaptiveSparsify_IPM

open Matrix

namespace AdaptiveSparsify

/-- **Lemma 4.11** (Basic Step Size Bounds), p.25.

Liu, Peng, Tang, Weng, Yang, *Adaptive Matrix Sparsification …* (manuscript, sha256 7a66a27b…), Lemma 4.11, p.25.

"In Algorithm 1 we have that 1. ‖g‖₂ ≤ α(ε² + 10βε)^{1/2} ≤ 1.01αε, 2. ‖δ₁‖₂ ≲ αε exp(ε), and 3. ‖δ₂‖₂ ≤
αε exp(3ε/2)."

**Formalization Note.** "In Algorithm 1" is written out: `(x, s)` is `ε` well-centered at `t` (the proof,
p.25, "we used that x and s are centered"), and the choice `x̄, s̄, H, τ̃` is valid. The printed range
`ε < 1/80` is kept and `C_center` is large, which the proof's `10βε ≤ 0.02ε²` and `3β ≤ ε` need. The
constant of `≲` is absolute. -/
theorem lemma_4_11 : ∃ C : ℝ, 0 < C ∧ ∀ CK : ℕ, 1 ≤ CK → ∀ ε : ℝ, 0 < ε → ε < 1 / 80 →
    ∃ Cc₀ : ℝ, 0 < Cc₀ ∧ ∀ Cc : ℝ, Cc₀ ≤ Cc →
      ∀ I : ERMInstance, I.IsAdmissible CK → 2 ≤ I.blocks.n →
      ∀ (t : ℝ) (x s : Fin I.blocks.n → ℝ) (ch : I.StepChoice), 0 < t →
        let p : Params := ⟨CK, ε, Cc⟩
        let α := p.alpha I.blocks.n
        let β := p.beta I.blocks.n
        I.WellCentered α ε t x s → ch.Valid p t x s →
        eNorm (ch.g p t) ≤ α * Real.sqrt (ε ^ 2 + 10 * β * ε) ∧
        α * Real.sqrt (ε ^ 2 + 10 * β * ε) ≤ 1.01 * α * ε ∧
        eNorm (ch.δ₁ p t) ≤ C * (α * ε * Real.exp ε) ∧
        eNorm (ch.δ₂ x) ≤ α * ε * Real.exp (3 * ε / 2) := by sorry

end AdaptiveSparsify
