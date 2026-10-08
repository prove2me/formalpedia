-- Prove2me | Theorems.Thm_Cohen2019_Tight_setA_inter_setB_null
-- name    : Cohen2019.Tight.setA_inter_setB_null
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:30:49.686003+00:00
-- url     : https://prove2.me/theorems/4559ddcf-9469-42dd-a197-13c4ab307259
-- title:
--   Proof of Theorem 2 — A ∩ B is 𝒩(x, σ²I)-null when p_A + p_B ≤ 1, and empty when p_A + p_B < 1 (corrected)
-- statement:
--   Let $\sigma>0$, $x,\delta\in\mathbb R^d$ with $\delta\ne0$, and $\underline{p_A},\overline{p_B}\in(0,1)$ with $\underline{p_A}+\overline{p_B}\le1$. Then
--   $$\mathcal N(x,\sigma^2I)(A\cap B)=0,$$
--   and if moreover $\underline{p_A}+\overline{p_B}<1$, then $A\cap B=\emptyset$.
--
--   This is what makes the worst-case classifier of Theorem 2, which equals $c_A$ on $A$ and $c_B$ on $B$, well defined up to a null set.
--
--   **Formalization Note.** The paper asserts $A\cap B=\emptyset$ under $\underline{p_A}+\overline{p_B}\le1$. At equality $\Phi^{-1}(\underline{p_A})=\Phi^{-1}(1-\overline{p_B})$ and $A\cap B$ is the hyperplane $\delta^T(z-x)=\sigma\|\delta\|\Phi^{-1}(\underline{p_A})$, so the printed claim is false there; the corrected statement replaces "empty" by "null" at equality.
-- source:
--   Cohen, Rosenfeld, Kolter, Certified Adversarial Robustness via Randomized Smoothing, arXiv:1902.02918v2, proof of Theorem 2, p. 15

import Mathlib
import Definitions.Def_Cohen2019_Tight_Model
import Definitions.Def_Cohen2019_Tight_HalfSpaces

open MeasureTheory ProbabilityTheory

namespace Cohen2019.Tight

/-- Cohen, Rosenfeld, Kolter, arXiv:1902.02918v2, proof of Theorem 2, p. 15: "This function is
well-defined, since `A ∩ B = ∅` provided that `p̲A + p̄B ≤ 1`."

As printed this is false at `p̲A + p̄B = 1`: then `Φ⁻¹(p̲A) = Φ⁻¹(1 − p̄B)` and `A ∩ B` is the
hyperplane `δᵀ(z − x) = σ‖δ‖Φ⁻¹(p̲A)`. Corrected statement: under `p̲A + p̄B ≤ 1` the
intersection is `𝒩(x, σ²I)`-null, and under `p̲A + p̄B < 1` it is empty.

**Formalization Note.** `δ ≠ 0`, `σ > 0` and `p̲A, p̄B ∈ (0, 1)` are added so that
`Φ⁻¹(p̲A)`, `Φ⁻¹(1 − p̄B)` are the paper's finite values. -/
theorem setA_inter_setB_null {d : ℕ} (x δ : Space d) (σ pA pB : ℝ) (hσ : 0 < σ) (hδ : δ ≠ 0)
    (hpA0 : 0 < pA) (hpA1 : pA < 1) (hpB0 : 0 < pB) (hpB1 : pB < 1) (hsum : pA + pB ≤ 1) :
    gaussNoise x σ (setA x δ σ pA ∩ setB x δ σ pB) = 0 ∧
      (pA + pB < 1 → setA x δ σ pA ∩ setB x δ σ pB = ∅) := by sorry

end Cohen2019.Tight
