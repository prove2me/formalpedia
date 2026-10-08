-- Prove2me | Theorems.Thm_Cohen2019_Tight_prob_Y_A_lt_B_iff
-- name    : Cohen2019.Tight.prob_Y_A_lt_B_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T18:31:14.137009+00:00
-- url     : https://prove2.me/theorems/b5b4201b-32f5-4ba2-ae29-3f6f498e4302
-- title:
--   Proof of Theorem 2 — ℙ(Y ∈ A) < ℙ(Y ∈ B) ⟺ ‖δ‖₂ > R
-- statement:
--   Let $\sigma>0$, $x,\delta\in\mathbb R^d$ with $\delta\ne0$, and $\underline{p_A},\overline{p_B}\in(0,1)$. Let $Y\sim\mathcal N(x+\delta,\sigma^2I)$, let $A$, $B$ be the half-spaces of the proof, and $R=\frac{\sigma}{2}\big(\Phi^{-1}(\underline{p_A})-\Phi^{-1}(\overline{p_B})\big)$. Then
--   $$\mathbb P(Y\in A)<\mathbb P(Y\in B)\iff\|\delta\|_2>R.$$
--
--   The certified radius of Theorem 1 is exactly the perturbation size at which the worst-case classifier's top class changes.
--
--   **Formalization Note.** Stated for the half-spaces themselves, not the one-dimensional reduction. $\delta\ne0$ and $\underline{p_A},\overline{p_B}\in(0,1)$ are added; neither $\underline{p_A}\ge\overline{p_B}$ nor $\underline{p_A}+\overline{p_B}\le1$ is needed.
-- source:
--   Cohen, Rosenfeld, Kolter, Certified Adversarial Robustness via Randomized Smoothing, arXiv:1902.02918v2, proof of Theorem 2, p. 15

import Mathlib
import Definitions.Def_Cohen2019_Tight_Model
import Definitions.Def_Cohen2019_Tight_HalfSpaces

open MeasureTheory ProbabilityTheory

namespace Cohen2019.Tight

/-- Cohen, Rosenfeld, Kolter, arXiv:1902.02918v2, proof of Theorem 2, p. 15: "It follows from
(13) and (14) that `ℙ(Y ∈ A) < ℙ(Y ∈ B) ⟺ ‖δ‖₂ > R`", for `Y ∼ 𝒩(x + δ, σ²I)` and
`R = (σ/2)(Φ⁻¹(p̲A) − Φ⁻¹(p̄B))`.

**Formalization Note.** Stated for the half-spaces `A`, `B` themselves (not the one-dimensional
reduction). `δ ≠ 0` and `p̲A, p̄B ∈ (0, 1)` are added, as in (13) and (14); the equivalence
needs neither `p̲A ≥ p̄B` nor `p̲A + p̄B ≤ 1`. -/
theorem prob_Y_A_lt_B_iff {d : ℕ} (x δ : Space d) (σ pA pB : ℝ) (hσ : 0 < σ) (hδ : δ ≠ 0)
    (hpA0 : 0 < pA) (hpA1 : pA < 1) (hpB0 : 0 < pB) (hpB1 : pB < 1) :
    (gaussNoise (x + δ) σ (setA x δ σ pA)).toReal < (gaussNoise (x + δ) σ (setB x δ σ pB)).toReal
      ↔ radius σ pA pB < ‖δ‖ := by sorry

end Cohen2019.Tight
