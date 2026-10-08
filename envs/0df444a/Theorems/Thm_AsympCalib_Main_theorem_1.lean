-- Prove2me | Theorems.Thm_AsympCalib_Main_theorem_1
-- name    : AsympCalib.Main.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:06:24.670975+00:00
-- url     : https://prove2.me/theorems/b6913d83-38d9-4450-85e4-91da2d2b25c3
-- title:
--   Theorem 1, p. 385 — regret-balancing grid forecast is ε-calibrated against adaptive Nature
-- statement:
--   Fix $\varepsilon>0$ and an integer grid parameter $k\ge1$ with $k\ge1/\varepsilon^2$. Let a randomized forecaster choose a grid probability $i/k$ after each finite history according to a distribution satisfying the regret-flow conservation equations (2), computed from earlier rounds. Nature may use any randomized rule depending on past realized forecasts and outcomes, but does not observe the current forecast draw. If $C_t$ is the realized quadratic calibration score, then there is a time $t_1$ such that
--
--   $$
--   \Pr_{\sigma,A}\{C_t<\varepsilon\}>1-\varepsilon
--   \qquad\text{for every }t\ge t_1.
--   $$
--
--   This identifies the particular regret-balancing algorithm as an $\varepsilon$-calibrated forecaster against every adaptive Nature. It is stronger in content than merely asserting that some calibrated forecaster exists.
--
--   **Formalization Note** The paper writes $k\simeq1/\varepsilon^2$; the statement uses $k\ge1/\varepsilon^2$. Its limit condition is expressed as an eventual strict probability bound; the proof yields convergence of this probability to $1$. The extra explicit $k>0$ prevents a degenerate grid. The grid has $k+1$ points, encoded as vectors $(1-i/k,i/k)$, and the vectors are distinct. Round $s$ uses the forecaster distribution from the history prefix before $s$, with $R_{s-1}$ represented by regret over that prefix. The event concerns the realized score $C_t$, not $\widetilde C_t$.
-- source:
--   Foster and Vohra, Asymptotic calibration, Biometrika 85 (1998), p. 385, Theorem 1; p. 383, Definition (ε-calibration); p. 388, Corollary (§6); https://doi.org/10.1093/biomet/85.2.379

import Mathlib
import Definitions.Def_AsympCalib_Main_Setting

noncomputable section

namespace AsympCalib.Main

theorem theorem_1 (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (hk0 : 0 < k) (hk : 1 / ε ^ 2 ≤ (k : ℝ))
    (σ : History → PMF (Fin (k + 1)))
    (hσ : IsConservationForecaster k σ)
    (A : History → PMF (Fin 2)) :
    ∃ t₁ : ℕ, ∀ t ≥ t₁,
      ENNReal.ofReal (1 - ε) <
        (CalibratedCE.Forecast.histLaw (forecaster k σ) A t).toOuterMeasure
          {h : History | CalibratedCE.Forecast.calibScore2Hj h 1 < ε} := by sorry

end AsympCalib.Main
