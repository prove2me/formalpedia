-- Prove2me | Theorems.Thm_DRMeanVar_Reform_proposition_3
-- name    : DRMeanVar.Reform.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:11.655123+00:00
-- url     : https://prove2.me/theorems/8db459f0-e068-4826-959e-ba942c8e929a
-- title:
--   Proposition 3, p. 5 — the mean-constrained worst second moment
-- statement:
--   Fix $n\ge1$, $\delta\ge0$, $1\le q<\infty$, and conjugate $p,q$. Write $m=E_{P_n}(\varphi^TR)$, $N=\|\varphi\|_p$, and $s^2=\operatorname{Var}_{P_n}(\varphi^TR)$. If $(\alpha-m)^2\le\delta N^2$, then the maximum second moment among laws $P\in U_\delta(P_n)$ with $E_P(\varphi^TR)=\alpha$ is attained and equals
--   $$h(\alpha,\varphi)=E_{P_n}[(\varphi^TR)^2]+2(\alpha-m)m+\delta N^2+2\sqrt{\delta N^2-(\alpha-m)^2}\sqrt{s^2}. $$
--
--   This evaluates the inner mean-constrained problem (7), which is used to recover the worst-case variance.
--
--   **Formalization Note** `IsGreatest` captures attainment of the maximum. The radicand is nonnegative by the stated feasibility condition. The standing sample, radius and exponent assumptions from §2.1 are explicit.
-- source:
--   Blanchet, Chen & Zhou, Distributionally Robust Mean-Variance Portfolio Selection with Wasserstein Distances, arXiv:1802.04885v1, p. 5, Proposition 3

import Mathlib
import Definitions.Def_DRMeanVar_Reform_Setting

open MeasureTheory

namespace DRMeanVar.Reform

/-- Proposition 3, p. 5: the attained value of the mean-constrained second-moment problem. -/
theorem proposition_3 {d n : ℕ} [NeZero n] (R : Fin n → (Fin d → ℝ))
    (q p : ENNReal) (δ α : ℝ) (hδ : 0 ≤ δ) (hq : 1 ≤ q) (hqtop : q ≠ ⊤)
    (hpq : p.HolderConjugate q) (φ : Fin d → ℝ)
    (hfeas : (α - empMean R φ) ^ 2 - δ * ‖WithLp.toLp p φ‖ ^ 2 ≤ 0) :
    IsGreatest {v : ℝ | ∃ P ∈ U q δ R, pMean P φ = α ∧ v = pSecond P φ}
      (hFun p δ R α φ) := by sorry

end DRMeanVar.Reform
