-- Prove2me | Theorems.Thm_DRMeanVar_Reform_thm1_proof_display_1
-- name    : DRMeanVar.Reform.thm1_proof_display_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:05.726358+00:00
-- url     : https://prove2.me/theorems/a85a026a-242e-40ed-a47b-172d22d61b22
-- title:
--   Proof of Theorem 1, p. 6 — the centered second moment is a square
-- statement:
--   For a sample of size $n\ge1$, portfolio $\varphi$, radius $\delta\ge0$, and mean level $\alpha$, write $m=E_{P_n}(\varphi^TR)$ and $N=\|\varphi\|_p$. Whenever $(\alpha-m)^2\le\delta N^2$,
--   $$h(\alpha,\varphi)-\alpha^2=\left(\sqrt{\operatorname{Var}_{P_n}(\varphi^TR)}+\sqrt{\delta N^2-(\alpha-m)^2}\right)^2.$$
--
--   This identifies the variance corresponding to the second-moment formula of Proposition 3.
--
--   **Formalization Note** The empirical variance uses $1/n$. The explicit radicand condition is implicit in the paper's use of Proposition 3.
-- source:
--   Blanchet, Chen & Zhou, Distributionally Robust Mean-Variance Portfolio Selection with Wasserstein Distances, arXiv:1802.04885v1, p. 6, §2.2, proof of Theorem 1, first display

import Mathlib
import Definitions.Def_DRMeanVar_Reform_Setting

open MeasureTheory

namespace DRMeanVar.Reform

/-- The first displayed identity in the proof of Theorem 1, p. 6. -/
theorem thm1_proof_display_1 {d n : ℕ} [NeZero n]
    (R : Fin n → (Fin d → ℝ)) (p : ENNReal) (δ α : ℝ) (φ : Fin d → ℝ)
    (hδ : 0 ≤ δ)
    (hfeas : (α - empMean R φ) ^ 2 - δ * ‖WithLp.toLp p φ‖ ^ 2 ≤ 0) :
    hFun p δ R α φ - α ^ 2 =
      (Real.sqrt (empVar R φ) +
        Real.sqrt (δ * ‖WithLp.toLp p φ‖ ^ 2 - (α - empMean R φ) ^ 2)) ^ 2 := by sorry

end DRMeanVar.Reform
