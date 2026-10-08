-- Prove2me | Theorems.Thm_AsympCalib_Main_S_eq_sq_sub_sq
-- name    : AsympCalib.Main.S_eq_sq_sub_sq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:06:28.071357+00:00
-- url     : https://prove2.me/theorems/bd563b7c-17f4-4aa9-aadc-076f0bfc3bfa
-- title:
--   §6, p. 387 — Brier regret as a difference of squared calibration errors
-- statement:
--   For grid points $i/k$ and $j/k$, any real outcome sequence $X_s$, and any sequence of probability vectors $\mu_s$ on the grid, the signed regret after $t$ rounds obeys
--
--   $$
--   S_t^{ij}=\widetilde n_t(i/k)\bigl(\widetilde\rho_t(i/k)-i/k\bigr)^2
--   -\widetilde n_t(i/k)\bigl(\widetilde\rho_t(i/k)-j/k\bigr)^2.
--   $$
--
--   This algebraic identity connects pairwise Brier-score regret to the weighted calibration score in Theorem 3.
--
--   **Formalization Note** The identity holds for real $X_s$; the surrounding calibration theorems restrict outcomes to $0$ or $1$. The page's middle line has $2(j-k)$ where expansion gives $2(j-i)$; the final identity, used here, has the correct sign and indices. Rounds are indexed from $0$, and $\mu_s$ is a probability vector so zero weighted count also gives zero weighted outcome count.
-- source:
--   Foster and Vohra, Asymptotic calibration, Biometrika 85 (1998), p. 387, §6, proof of Theorem 3, first display; https://doi.org/10.1093/biomet/85.2.379

import Mathlib
import Definitions.Def_AsympCalib_Main_Setting

noncomputable section

namespace AsympCalib.Main

theorem S_eq_sq_sub_sq (k : ℕ) (hk : 0 < k) (X : ℕ → ℝ)
    (μ : ℕ → Fin (k + 1) → ℝ)
    (hμ : ∀ s, CalibratedCE.Forecast.IsDist (μ s))
    (t : ℕ) (i j : Fin (k + 1)) :
    CalibratedCE.Forecast.S (brierLoss k X) μ t i j =
      nTilde k μ t i * (rhoTilde k X μ t i - gridPt k i) ^ 2 -
      nTilde k μ t i * (rhoTilde k X μ t i - gridPt k j) ^ 2 := by sorry

end AsympCalib.Main
