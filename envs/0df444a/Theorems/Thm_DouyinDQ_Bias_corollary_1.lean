-- Prove2me | Theorems.Thm_DouyinDQ_Bias_corollary_1
-- name    : DouyinDQ.Bias.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:05:30.83665+00:00
-- url     : https://prove2.me/theorems/e775418d-c23d-43c2-9063-ca3b337a19e5
-- title:
--   Corollary 1, p. 8 — absorbing-case Kth-order remainder
-- statement:
--   In the absorbing total-reward setting of Theorem 2, suppose the distance between the transition rows of $P_\pi$ and $P_{\pi'}$ is at most $\delta$ at every state. Write $r_{\max}=\max_s|r_{\pi'}(s)|$. Then for every $K\ge0$,
--   $$
--   \left|\widetilde E_{\pi'}r_{\pi'}-\sum_{k=0}^{K}\widetilde E_\pi DQ^{(k)}_{\pi,\pi'}\right|\le(\delta T_{\rm abs})^{K+1}T_{\rm abs}r_{\max}.
--   $$
--   This is Corollary 1 with the absorbing row of Table 1: both the effective horizon and value-functional scale are $T_{\rm abs}$.
--
--   **Formalization Note** The paper does not define $D_{\rm TV}$. Here it is the total-variation norm $\sum_{s'}|P_\pi(s,s')-P_{\pi'}(s,s')|$. Under the convention of half that sum, the printed constant fails, with ratios approaching $2$.
-- source:
--   Farias, Li, Peng, Ren, Zhang, Zheng, Correcting for Interference in Experiments: A Case Study at Douyin, arXiv:2305.02542v1, p. 8, Corollary 1 and Table 1

import Definitions.Def_DouyinDQ_Bias_Model

namespace DouyinDQ.Bias

/-- Corollary 1, p. 8, with Table 1's absorbing-case constants. -/
theorem corollary_1 {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A]
    (M : MDP S A) (hM : M.Standing)
    (Sabs : Set S) [DecidablePred (· ∈ Sabs)] (Tabs δ : ℝ)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π')
    (habsπ : IsAbsorbingFor M Sabs π) (htπ : AbsTimeLT M Sabs π Tabs)
    (habsπ' : IsAbsorbingFor M Sabs π') (htπ' : AbsTimeLT M Sabs π' Tabs)
    (hδ : ∀ s, ∑ s', |Ppol M π s s' - Ppol M π' s s'| ≤ δ)
    (K : ℕ) :
    |Etilde M π' (rpol M π') -
      ∑ k ∈ Finset.range (K + 1), Etilde M π (DQ M π π' k)| ≤
      (δ * Tabs) ^ (K + 1) * Tabs * (⨆ s, |rpol M π' s|) := by sorry

end DouyinDQ.Bias
