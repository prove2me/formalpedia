-- Prove2me | Theorems.Thm_AsympCalib_Main_exists_conservation_forecaster
-- name    : AsympCalib.Main.exists_conservation_forecaster
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:06:23.607557+00:00
-- url     : https://prove2.me/theorems/d864a1a4-5a61-45ec-bc63-57546a8a7f15
-- title:
--   §5, p. 385 — a history-adapted regret-balancing forecaster exists
-- statement:
--   Fix an integer $k\ge1$ and the grid $G_k=\{0,1/k,\ldots,1\}$. There exists a randomized forecasting rule $\sigma$ that assigns a probability vector on $G_k$ to every finite history and, at every history $h$, satisfies the regret-flow equations
--
--   $$
--   \sigma(h)_i\sum_j R_{|h|}^{i\to j}(h)
--   =\sum_j\sigma(h)_j R_{|h|}^{j\to i}(h)\qquad(0\le i\le k).
--   $$
--
--   Here the regrets are computed from the outcomes and the earlier mixtures along the prefixes of $h$. This existence claim establishes that the algorithm used by Theorem 1 can actually be run.
--
--   **Formalization Note** The page proves pointwise solvability of (2); the statement packages those solutions into a history-adapted rule. Its full sums include diagonal terms that cancel. The parameter $k>0$ makes the grid meaningful.
-- source:
--   Foster and Vohra, Asymptotic calibration, Biometrika 85 (1998), p. 385, §5, conclusion after (3)–(4); https://doi.org/10.1093/biomet/85.2.379

import Mathlib
import Definitions.Def_AsympCalib_Main_Setting

noncomputable section

namespace AsympCalib.Main

theorem exists_conservation_forecaster (k : ℕ) (hk : 0 < k) :
    ∃ σ : History → PMF (Fin (k + 1)), IsConservationForecaster k σ := by sorry

end AsympCalib.Main
