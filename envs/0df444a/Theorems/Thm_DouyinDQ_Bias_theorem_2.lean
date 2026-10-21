-- Prove2me | Theorems.Thm_DouyinDQ_Bias_theorem_2
-- name    : DouyinDQ.Bias.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:05:37.017109+00:00
-- url     : https://prove2.me/theorems/7ba4773d-7588-4593-9522-9e9514276c1f
-- title:
--   Theorem 2, p. 7 — total-reward expansion under Assumption 5
-- statement:
--   Consider two stationary policies $\pi,\pi'$ on a finite stochastic MDP. Both have a closed zero-reward absorbing class, and their expected times outside it are strictly below $T_{\rm abs}$ from every starting state. Let $\widetilde E_\pi$ be the total-reward value functional, and define $DQ^{(0)}_{\pi,\pi'}=r_{\pi'}$ and the higher terms by the paper's differences of state-reward $Q$ functions. For every $K\ge0$,
--   $$
--   \widetilde E_{\pi'}r_{\pi'}=\sum_{k=0}^{K}\widetilde E_\pi DQ^{(k)}_{\pi,\pi'}+\widetilde E_{\pi'}DQ^{(K+1)}_{\pi,\pi'}.
--   $$
--   The last term is the exact remainder. This is Theorem 2 in the absorbing total-reward setting of Assumption 5.
--
--   **Formalization Note** The paper abbreviates the left reward as $r$; Section 5.1 identifies the policy objective as $\widetilde E_{\pi'}r_{\pi'}$. Stochasticity and valid stationary policies are explicit in Lean.
-- source:
--   Farias, Li, Peng, Ren, Zhang, Zheng, Correcting for Interference in Experiments: A Case Study at Douyin, arXiv:2305.02542v1, p. 7, Theorem 2 and Assumption 5

import Definitions.Def_DouyinDQ_Bias_Model

namespace DouyinDQ.Bias

/-- Theorem 2, p. 7, under Assumption 5 (absorbing total reward). -/
theorem theorem_2 {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A]
    (M : MDP S A) (hM : M.Standing)
    (Sabs : Set S) [DecidablePred (· ∈ Sabs)] (Tabs : ℝ)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π')
    (habsπ : IsAbsorbingFor M Sabs π) (htπ : AbsTimeLT M Sabs π Tabs)
    (habsπ' : IsAbsorbingFor M Sabs π') (htπ' : AbsTimeLT M Sabs π' Tabs)
    (K : ℕ) :
    Etilde M π' (rpol M π') =
      (∑ k ∈ Finset.range (K + 1), Etilde M π (DQ M π π' k)) +
        Etilde M π' (DQ M π π' (K + 1)) := by sorry

end DouyinDQ.Bias
