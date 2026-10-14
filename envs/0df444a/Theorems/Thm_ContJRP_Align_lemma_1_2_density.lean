-- Prove2me | Theorems.Thm_ContJRP_Align_lemma_1_2_density
-- name    : ContJRP.Align.lemma_1_2_density
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:51:03.132782+00:00
-- url     : https://prove2.me/theorems/342d212c-3270-49a3-8e5d-0b20529557a4
-- title:
--   Lemma 1.2, p. 3 — the ordering density lim N(T,Δ)/Δ exists and equals Σ_{N} (−1)^{|N|+1}/M_N
-- statement:
--   Let $(T_i)_{i\in s}$ be a finite family of positive intervals, $N(T,\Delta)=\big|\bigcup_{i\in s}\mathcal M_{T_i,\Delta}\big|$ the number of joint orders in $[0,\Delta]$, and $M_{\mathcal N}$ the least common multiple of $\{T_i\}_{i\in\mathcal N}$ ($M_{\mathcal N}=\infty$, $1/M_{\mathcal N}=0$, if there is none). Then the limit exists and
--   $$\lim_{\Delta\to\infty}\frac{N(T,\Delta)}{\Delta}=\sum_{\emptyset\ne\mathcal N\subseteq s}\frac{(-1)^{|\mathcal N|+1}}{M_{\mathcal N}} .$$
--
--   This makes the joint ordering cost $J(T)$ of (1) well defined for every policy with positive intervals, and gives it in closed form.
--
--   **Formalization Note** The statement is a `Tendsto` (existence of the limit plus its value), not an identity about `limUnder`. It is stated over an arbitrary finite index set, a generalization of the page's $[n]$ used later for sets of representatives. The page's sum over $\mathcal N\subseteq[n]$ ranges over nonempty $\mathcal N$, as inclusion–exclusion requires ($M_\emptyset$ is undefined).
-- source:
--   Segev, The Continuous-Time Joint Replenishment Problem: ϵ-Optimal Policies via Pairwise Alignment, arXiv:2302.09941v1, p. 3, Lemma 1.2 (proof in §4.1, pp. 17–18)

import Mathlib
import Definitions.Def_ContJRP_Align_Model

namespace ContJRP.Align

theorem lemma_1_2_density {ι : Type*} (s : Finset ι) (T : ι → ℝ) (hT : ∀ i ∈ s, 0 < T i) :
    Filter.Tendsto (fun Δ : ℝ => (numOrders s T Δ : ℝ) / Δ) Filter.atTop
      (nhds (∑ N ∈ s.powerset.filter (fun N => N.Nonempty),
        (-1 : ℝ) ^ (N.card + 1) * invLcm N T)) := by sorry

end ContJRP.Align
