-- Prove2me | Theorems.Thm_BayesEnsemble_GenProbit_lemma_1_i
-- name    : BayesEnsemble.GenProbit.lemma_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:10.040146+00:00
-- url     : https://prove2.me/theorems/71f4016d-9842-4f4b-aa54-68806c0abf7a
-- title:
--   Lemma 1(i), p. 27 — the linear predictor is normal
-- statement:
--   Let $x\sim N(\mu,\Sigma)$, with $\Sigma$ a covariance matrix, and let $\alpha_0,\alpha_1,\ldots,\alpha_k$ be real. The linear predictor has the normal law
--
--   $$
--   \alpha_0+\sum_{i=1}^k\alpha_i x_i\sim N(m_0,v_0),\qquad
--   m_0=\alpha_0+\sum_i\alpha_i\mu_i,\quad
--   v_0=\sum_{i,j}\alpha_i\alpha_j\sigma_{ij}.
--   $$
--
--   This is the distributional input for the prior-predictive calculation in Proposition 4. **Formalization Note** The statement is an equality of pushforward measures. The variance is converted to a nonnegative real, justified by positive semidefiniteness; no coefficient nondegeneracy is needed for this part of Lemma 1.
-- source:
--   Lichtendahl, Grushka-Cockayne, Jose & Winkler, Bayesian Ensembles of Binary-Event Forecasts: When Is It Appropriate to Extremize or Anti-Extremize?, arXiv:1705.02391v2, p. 27, Lemma 1(i)

import Mathlib
import Definitions.Def_BayesEnsemble_GenProbit_Model

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace BayesEnsemble.GenProbit

/-- Lemma 1(i), p. 27: the linear predictor is Gaussian. -/
theorem lemma_1_i {k : ℕ} (P : Params k) (hS : P.S.PosSemidef) :
    (multivariateGaussian P.mean P.S).map
      (fun y => P.alpha0 + ∑ i, P.alpha i * y i) =
      gaussianReal (m0 P) (v0 P).toNNReal := by sorry

end BayesEnsemble.GenProbit
