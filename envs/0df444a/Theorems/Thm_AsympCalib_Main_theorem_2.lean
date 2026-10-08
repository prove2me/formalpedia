-- Prove2me | Theorems.Thm_AsympCalib_Main_theorem_2
-- name    : AsympCalib.Main.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:06:24.829856+00:00
-- url     : https://prove2.me/theorems/9a68fdf8-c4a2-4b77-94f0-3532c6260c1b
-- title:
--   Theorem 2, p. 386 — realized and weighted calibration scores agree in probability
-- statement:
--   Fix a grid with $k\ge1$ and any history-dependent randomized forecaster $\sigma$ on that grid. Nature may choose any randomized outcome rule $A$ based on the past. Let $C_t$ be the realized quadratic calibration score and $\widetilde C_t$ the same score with each forecast indicator replaced by its conditional probability. Then, for every $\eta>0$,
--
--   $$
--   \Pr_{\sigma,A}\{|C_t-\widetilde C_t|\ge\eta\}\longrightarrow 0\qquad(t\to\infty).
--   $$
--
--   This result transfers a deterministic bound on $\widetilde C_t$ into a high-probability bound on the actual score.
--
--   **Formalization Note** The probability is the outer measure of the event under the finite-history law. The actual score is the wet-outcome component of the published quadratic calibration score. The vectors $(1-i/k,i/k)$ are distinct for $k>0$. No conservation condition is assumed: the claim holds for every adapted mixture rule.
-- source:
--   Foster and Vohra, Asymptotic calibration, Biometrika 85 (1998), p. 386, Theorem 2; https://doi.org/10.1093/biomet/85.2.379

import Mathlib
import Definitions.Def_AsympCalib_Main_Setting

noncomputable section

namespace AsympCalib.Main

theorem theorem_2 (k : ℕ) (hk : 0 < k)
    (σ : History → PMF (Fin (k + 1)))
    (A : History → PMF (Fin 2))
    (η : ℝ) (hη : 0 < η) :
    Filter.Tendsto
      (fun t : ℕ =>
        (CalibratedCE.Forecast.histLaw (forecaster k σ) A t).toOuterMeasure
          {h : History |
            η ≤ |CalibratedCE.Forecast.calibScore2Hj h 1 - CTildeH k σ h|})
      Filter.atTop (nhds 0) := by sorry

end AsympCalib.Main
