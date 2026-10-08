-- Prove2me | Theorems.Thm_AsympCalib_Main_theorem_4
-- name    : AsympCalib.Main.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:06:39.555982+00:00
-- url     : https://prove2.me/theorems/738ead01-0a00-4a1d-a25b-363fe79caaf3
-- title:
--   Theorem 4, pp. 387–388 — the smoothed regret potential is at most tkδ
-- statement:
--   Let $k\ge1$, let $X_s\in\{0,1\}$, and let every $\mu_s$ be a probability vector on the grid satisfying the regret conservation equation (2) at its round. For each $\delta>0$ and $t\ge0$,
--
--   $$
--   \widetilde R_t^\delta\le tk\delta.
--   $$
--
--   This is the deterministic potential bound that closes the regret estimate for the paper's forecasting rule.
--
--   **Formalization Note** Regret in the equation for round $s$ is computed over earlier rounds only. The $k$ in the bound counts the other grid points $j\ne i$ for each $i$; it is correct even though the grid has $k+1$ points. Full sums in the Lean conservation equation cancel their diagonal terms.
-- source:
--   Foster and Vohra, Asymptotic calibration, Biometrika 85 (1998), pp. 387–388, Theorem 4; https://doi.org/10.1093/biomet/85.2.379

import Mathlib
import Definitions.Def_AsympCalib_Main_Setting

noncomputable section

namespace AsympCalib.Main

theorem theorem_4 (k : ℕ) (hk : 0 < k) (X : ℕ → ℝ)
    (hX : ∀ s, X s = 0 ∨ X s = 1)
    (μ : ℕ → Fin (k + 1) → ℝ)
    (hμ : ∀ s, CalibratedCE.Forecast.IsDist (μ s))
    (hcons : ∀ s, Conservation k X μ s)
    (δ : ℝ) (hδ : 0 < δ) (t : ℕ) :
    RTilde k X μ δ t ≤ (t : ℝ) * (k : ℝ) * δ := by sorry

end AsympCalib.Main
