-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_rts_smoothing_covariance_improves_psd
-- name    : AppliedSDE.SarkkaSolin.rts_smoothing_covariance_improves_psd
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:55:07.003616+00:00
-- url     : https://prove2.me/theorems/22957464-bf05-4ba5-994b-029e66d481e1
-- title:
--   RTS smoother covariance is no greater than filtered covariance in Loewner order
-- statement:
--   Original derived from Algorithm 10.28 and covariance recursion (10.91), printed p. 225. Let Pk be the filtered covariance, P_{k+1|k} the one-step predicted covariance, Jk the RTS smoother gain and P_{k+1|T} the next smoothed covariance. The RTS update is P_{k|T}=Pk+Jk(P_{k+1|T}−P_{k+1|k})Jkᵀ. If the next smoothed covariance is Loewner-below the predicted covariance, prove the current smoothed covariance is Loewner-below the filtered covariance for any finite state dimension. This is a matrix-valued covariance monotonicity lemma, rather than full posterior smoothing correctness.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   P_{k\mid T}=P_{k\mid k}+J_k(P_{k+1\mid T}-P_{k+1\mid k})J_k^\top\preceq P_{k\mid k}
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Algorithm 10.28, equation (10.91), RTS smoother PSD identity, printed pp. 224–225. https://doi.org/10.1017/9781108186735

import Mathlib
open MeasureTheory
open scoped BigOperators Topology

theorem AppliedSDE.SarkkaSolin.rts_smoothing_covariance_improves_psd
    (n : ℕ)
    (J Pf Ppred Pnext Psmooth : Matrix (Fin n) (Fin n) ℝ)
    (hupdate : Psmooth = Pf + J * (Pnext - Ppred) * J.transpose)
    (hnext : ∀ v : Fin n → ℝ,
      0 ≤ ∑ i : Fin n, v i * ((Ppred - Pnext).mulVec v) i) :
    ∀ v : Fin n → ℝ,
      0 ≤ ∑ i : Fin n, v i * ((Pf - Psmooth).mulVec v) i := by
  sorry
