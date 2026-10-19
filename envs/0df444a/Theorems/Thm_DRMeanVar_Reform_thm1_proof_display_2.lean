-- Prove2me | Theorems.Thm_DRMeanVar_Reform_thm1_proof_display_2
-- name    : DRMeanVar.Reform.thm1_proof_display_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:06.198353+00:00
-- url     : https://prove2.me/theorems/c7d66578-375b-4061-91ba-cedac08654f1
-- title:
--   Proof of Theorem 1, p. 6 — optimize over the adversarial mean
-- statement:
--   Fix a feasible portfolio $\varphi\in F_{\delta,\bar\alpha}(n)$, with $n\ge1$, $\delta\ge0$, $1\le q<\infty$, and conjugate $p,q$. Put $m=E_{P_n}(\varphi^TR)$ and $N=\|\varphi\|_p$. The maximum over $\alpha\ge\bar\alpha$ satisfying $(\alpha-m)^2\le\delta N^2$ is attained at $\alpha=m\ge\bar\alpha$, and
--   $$\max_{\alpha\ge\bar\alpha,\,(\alpha-m)^2\le\delta N^2}[h(\alpha,\varphi)-\alpha^2]=\left(\sqrt{\operatorname{Var}_{P_n}(\varphi^TR)}+\sqrt\delta\,N\right)^2.$$
--
--   This is the final scalar maximization in the proof of Theorem 1.
--
--   **Formalization Note** The statement records both the maximum value and the attaining mean. The feasible portfolio hypothesis supplies $m\ge\bar\alpha$.
-- source:
--   Blanchet, Chen & Zhou, Distributionally Robust Mean-Variance Portfolio Selection with Wasserstein Distances, arXiv:1802.04885v1, p. 6, §2.2, proof of Theorem 1, second display

import Mathlib
import Definitions.Def_DRMeanVar_Reform_Setting

open MeasureTheory

namespace DRMeanVar.Reform

/-- The second displayed maximum and its attaining mean in the proof of Theorem 1, p. 6. -/
theorem thm1_proof_display_2 {d n : ℕ} [NeZero n]
    (R : Fin n → (Fin d → ℝ)) (q p : ENNReal) (δ αbar : ℝ)
    (hδ : 0 ≤ δ) (hq : 1 ≤ q) (hqtop : q ≠ ⊤)
    (hpq : p.HolderConjugate q) (φ : Fin d → ℝ) (hφ : φ ∈ F q δ αbar R) :
    IsGreatest ((fun α => hFun p δ R α φ - α ^ 2) ''
      {α : ℝ | αbar ≤ α ∧ (α - empMean R φ) ^ 2 - δ * ‖WithLp.toLp p φ‖ ^ 2 ≤ 0})
      (dualObj p δ R φ) ∧
    αbar ≤ empMean R φ ∧
    hFun p δ R (empMean R φ) φ - (empMean R φ) ^ 2 = dualObj p δ R φ := by sorry

end DRMeanVar.Reform
