-- Prove2me | Theorems.Thm_DouyinDQ_Bias_k1_identity
-- name    : DouyinDQ.Bias.k1_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:05:47.228985+00:00
-- url     : https://prove2.me/theorems/a626176d-cc95-4e82-9b91-528dc3f1c3a5
-- title:
--   §5.3, p. 8 — corrected first-order identity for DQ
-- statement:
--   In the paper's absorbing experiment, the expectations of truncated DQ estimators converge to the difference between the first-order policy-value expansions for global treatment and global control, each evaluated under the experimental policy $\pi_{1/2}$:
--   $$
--   \lim_{H\to\infty}\mathbb E_{\pi_{1/2}}[\widehat{\rm ATE}^{(H)}_{\rm DQ}]
--   =\widetilde E_{\pi_{1/2}}(DQ^{(0)}_{\pi_{1/2},\pi_1}+DQ^{(1)}_{\pi_{1/2},\pi_1})
--   -\widetilde E_{\pi_{1/2}}(DQ^{(0)}_{\pi_{1/2},\pi_0}+DQ^{(1)}_{\pi_{1/2},\pi_0}).
--   $$
--   This identifies the estimator from equation (4) with the first-order approximation used to derive Theorem 1.
--
--   **Formalization Note** The printed display uses $\widetilde E_{\pi_1}$ and $\widetilde E_{\pi_0}$ as the outer functionals. Those make the zeroth-order terms equal the target rewards, contradicting the claimed estimator identity and Theorem 2. The data-policy functional $\widetilde E_{\pi_{1/2}}$ is the corrected reading.
-- source:
--   Farias, Li, Peng, Ren, Zhang, Zheng, Correcting for Interference in Experiments: A Case Study at Douyin, arXiv:2305.02542v1, p. 8, §5.3, K = 1 display (corrected outer value functional)

import Definitions.Def_DouyinDQ_Bias_Model

namespace DouyinDQ.Bias

/-- Section 5.3, p. 8: the DQ expectation is the first-order expansion,
with the data-policy value functional in both terms. -/
theorem k1_identity {S : Type} [Fintype S] [DecidableEq S]
    (M : MDP S (Fin 2)) (hM : M.Standing)
    (Sabs : Set S) [DecidablePred (· ∈ Sabs)] (Tabs : ℝ)
    (hA1 : Assumption1 M Sabs Tabs) :
    Filter.Tendsto (fun H => expDQTrunc M H) Filter.atTop
      (nhds (Etilde M piHalf (fun s =>
          DQ M piHalf pi1 0 s + DQ M piHalf pi1 1 s) -
        Etilde M piHalf (fun s =>
          DQ M piHalf pi0 0 s + DQ M piHalf pi0 1 s))) := by sorry

end DouyinDQ.Bias
