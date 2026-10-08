-- Prove2me | Theorems.Thm_AsympCalib_Main_theorem_3
-- name    : AsympCalib.Main.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:06:15.990056+00:00
-- url     : https://prove2.me/theorems/0756947e-be3f-4215-9be4-30e51ff34d41
-- title:
--   Theorem 3, p. 387 — regret sandwich with corrected grid count
-- statement:
--   Fix $k\ge1$, a binary outcome sequence $X_s$, probability vectors $\mu_s$ on the grid, a parameter $\delta>0$, and a horizon $t$. Write $M_i=\max_{0\le j\le k}R_t^{i\to j}$ and $\widetilde R_t^\delta=\sum_{i,j}g_\delta(R_t^{i\to j})$. Then
--
--   $$
--   \sum_i M_i\le t\widetilde C_t
--   \le\sum_i M_i+\frac{t}{4k^2}
--   \le\widetilde R_t^\delta+\frac{k+1}{2\delta}+\frac{t}{4k^2}.
--   $$
--
--   The inequalities turn the weighted calibration score into a quantity controlled by the smoothed regret potential.
--
--   **Formalization Note** The printed final constant is $k/(2\delta)$. The grid contains $k+1$ points, and summing the rowwise inequality $M_i\le 1/(2\delta)+\sum_jg_\delta(R_t^{i\to j})$ gives $(k+1)/(2\delta)$. The printed term can fail: if every row has exactly one positive regret $r$, then $\sum_iM_i=(k+1)r$, while $\min_{\delta>0}\{(k+1)\delta r^2/2+k/(2\delta)\}=r\sqrt{k(k+1)}<(k+1)r$. The statement therefore uses the corrected constant. The binary-outcome and probability-vector assumptions are the standing conventions of the paper. At $t=0$ all scores and regrets are zero.
-- source:
--   Foster and Vohra, Asymptotic calibration, Biometrika 85 (1998), p. 387, Theorem 3; proof, final paragraph; https://doi.org/10.1093/biomet/85.2.379

import Mathlib
import Definitions.Def_AsympCalib_Main_Setting

noncomputable section

namespace AsympCalib.Main

theorem theorem_3 (k : ℕ) (hk : 0 < k) (X : ℕ → ℝ)
    (hX : ∀ s, X s = 0 ∨ X s = 1)
    (μ : ℕ → Fin (k + 1) → ℝ)
    (hμ : ∀ s, CalibratedCE.Forecast.IsDist (μ s))
    (δ : ℝ) (hδ : 0 < δ) (t : ℕ) :
    let M := fun i : Fin (k + 1) =>
      (Finset.univ : Finset (Fin (k + 1))).sup' Finset.univ_nonempty
        (fun j => CalibratedCE.Forecast.Rg (brierLoss k X) μ t i j)
    (∑ i : Fin (k + 1), M i) ≤ (t : ℝ) * CTilde k X μ t ∧
    (t : ℝ) * CTilde k X μ t ≤
      (∑ i : Fin (k + 1), M i) + (t : ℝ) / (4 * (k : ℝ) ^ 2) ∧
    (∑ i : Fin (k + 1), M i) + (t : ℝ) / (4 * (k : ℝ) ^ 2) ≤
      RTilde k X μ δ t + ((k : ℝ) + 1) / (2 * δ) +
        (t : ℝ) / (4 * (k : ℝ) ^ 2) := by sorry

end AsympCalib.Main
