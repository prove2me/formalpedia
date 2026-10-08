-- Prove2me | Theorems.Thm_AsympCalib_Main_corollary_C_tilde_le
-- name    : AsympCalib.Main.corollary_C_tilde_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:08:04.37902+00:00
-- url     : https://prove2.me/theorems/c6fce0d3-0124-4edb-a8d9-09ad3173a089
-- title:
--   Corollary (§6), p. 388 — weighted calibration bound with corrected horizon
-- statement:
--   Let $\varepsilon>0$, choose an integer $k\ge1$ with $\varepsilon k^2>1$, and use probability-vector mixtures $\mu_s$ that satisfy equation (2) against a binary outcome sequence. For every horizon satisfying $t>8k^2/\varepsilon^2$,
--
--   $$
--   \widetilde C_t\le\varepsilon.
--   $$
--
--   This is the deterministic first part of the paper's corollary, which combines Theorems 3 and 4 before Theorem 2 transfers the result to realized forecasts.
--
--   **Formalization Note** The paper prints $t_0>8k^2/\varepsilon$. Its regret estimates give a term of order $k/\sqrt t$, which requires $t$ of order $k^2/\varepsilon^2$ for a bound by $\varepsilon$. The statement uses the corrected square. The page's $k>\varepsilon^{-1/2}$ is written equivalently as $1<\varepsilon k^2$. The condition $k>0$ fixes the grid; rounds are indexed from $0$.
-- source:
--   Foster and Vohra, Asymptotic calibration, Biometrika 85 (1998), p. 388, Corollary (§6), first sentence; https://doi.org/10.1093/biomet/85.2.379

import Mathlib
import Definitions.Def_AsympCalib_Main_Setting

noncomputable section

namespace AsympCalib.Main

theorem corollary_C_tilde_le (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (hk0 : 0 < k) (hk : 1 < ε * (k : ℝ) ^ 2)
    (X : ℕ → ℝ) (hX : ∀ s, X s = 0 ∨ X s = 1)
    (μ : ℕ → Fin (k + 1) → ℝ)
    (hμ : ∀ s, CalibratedCE.Forecast.IsDist (μ s))
    (hcons : ∀ s, Conservation k X μ s)
    (t : ℕ) (ht : 8 * (k : ℝ) ^ 2 / ε ^ 2 < (t : ℝ)) :
    CTilde k X μ t ≤ ε := by sorry

end AsympCalib.Main
