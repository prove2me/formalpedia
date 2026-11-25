-- Prove2me | Theorems.Thm_Arxiv2606_14486_uniform_phase_rotation
-- name    : Arxiv2606_14486.uniform_phase_rotation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T19:11:13.958213+00:00
-- url     : https://prove2.me/theorems/ee10f260-4244-490f-bd3f-44037f519e4e
-- title:
--   Sec. II-B, after eq. (11): weights rotated by a common phase $\kappa$
-- statement:
--   Let an array of $n$ elements, $k,d>0$, $\theta_1,\theta_2>0$, and a finite set $\mathcal{B}\subset\mathbb{C}$ of diode-state reflection coefficients be given. Let $\tilde w\in\mathcal{B}^n$ maximise
--
--   $$|G(-\theta_1,\theta_2)|=\Big|\sum_{i=1}^n w_i\exp\big(j(i-1)kd[\sin\theta_2-\sin\theta_1]\big)\Big|$$
--
--   over $w\in\mathcal{B}^n$ (eqs. 9-10). Suppose that under reverse illumination every weight is rotated by the same phase, $\tau_i=e^{j\kappa}\tilde w_i$, and let $G(\theta_2,-\theta_1)=\sum_i\tau_i\exp\big(j(i-1)kd[\sin\theta_2-\sin\theta_1]\big)$ (eq. 11). Then:
--
--   1. $G(\theta_2,-\theta_1)=e^{j\kappa}\,G(-\theta_1,\theta_2)$.
--   2. $|G(\theta_2,-\theta_1)|=|G(-\theta_1,\theta_2)|$.
--   3. The reverse gain is optimal: $|G(\theta_2,-\theta_1)|$ at $\tau$ is at least its value at any $w\in\mathcal{B}^n$.
--   4. If $G(-\theta_1,\theta_2)\ne0$, then $G(\theta_2,-\theta_1)=G(-\theta_1,\theta_2)$ holds if and only if $\kappa\in2\pi\mathbb{Z}$.
--
--   The paper reads item 4 as the failure of reciprocity under the array-factor approach for $\kappa\not\equiv0$.
--
--   **Formalization Note** Item 3 makes precise the paper's phrase "optimal gain in the reverse direction": the reverse problem is posed over the same set $\mathcal{B}^n$. The hypothesis $G(-\theta_1,\theta_2)\ne0$ in item 4 is implicit in the paper. If the optimum is $0$, for example when $\mathcal{B}$ is a single point and the exponentials cancel, the equality holds for every $\kappa$. The paper's premise that reciprocity requires the complex equality is not part of the statement.
-- source:
--   Khankhoje and Kundu, Implications of the Reciprocity Theorem for Reconfigurable Intelligent Surfaces, arXiv:2606.14486v1 (2026), claim c017; Sec. II-B (RIS with discrete phase shifts), eqs. (9)-(11) and the paragraph after eq. (11), PDF pp. 2-3

import Mathlib
import Definitions.Def_Arxiv2606_14486_Basic

open MeasureTheory

namespace Arxiv2606_14486

theorem uniform_phase_rotation {n : ℕ} (B : Finset ℂ) (k d θ₁ θ₂ : ℝ) (hk : 0 < k) (hd : 0 < d)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (wt : Fin n → ℂ)
    (hopt : IsOptimalWeights B n k d (-θ₁) θ₂ wt) (κ : ℝ) (τ : Fin n → ℂ)
    (hτ : ∀ i, τ i = Complex.exp ((κ : ℂ) * Complex.I) * wt i) :
    arrayFactor n k d θ₂ (-θ₁) τ =
        Complex.exp ((κ : ℂ) * Complex.I) * arrayFactor n k d (-θ₁) θ₂ wt ∧
      ‖arrayFactor n k d θ₂ (-θ₁) τ‖ = ‖arrayFactor n k d (-θ₁) θ₂ wt‖ ∧
      (∀ w : Fin n → ℂ, (∀ i, w i ∈ B) →
        ‖arrayFactor n k d θ₂ (-θ₁) w‖ ≤ ‖arrayFactor n k d θ₂ (-θ₁) τ‖) ∧
      (arrayFactor n k d (-θ₁) θ₂ wt ≠ 0 →
        (arrayFactor n k d θ₂ (-θ₁) τ = arrayFactor n k d (-θ₁) θ₂ wt ↔
          ∃ m : ℤ, κ = 2 * m * Real.pi)) := by sorry

end Arxiv2606_14486
