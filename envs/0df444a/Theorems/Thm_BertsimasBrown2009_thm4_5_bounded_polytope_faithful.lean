-- Prove2me | Theorems.Thm_BertsimasBrown2009_thm4_5_bounded_polytope_faithful
-- name    : BertsimasBrown2009.thm4_5_bounded_polytope_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T02:26:32.406991+00:00
-- url     : https://prove2.me/theorems/5e3633fe-8a7f-406e-a921-f312fb7b19d2
-- title:
--   Theorem 4.5 for a bounded polytope $\mathcal U$ (LP (15) and bound (16))
-- statement:
--   Let $N \ge 1$, let $\hat q \in \hat\Delta^N_{\mathrm{sym}}$ be a centrally symmetric generator, let $\mathcal A = \{a_1,\dots,a_N\} \subset \mathbb R^n$ have sample mean $\hat a = Ae_N$, and let $\mathcal U = \{a \in \mathbb R^n : u_k'a \ge v_k,\ k = 1,\dots,m\}$ be a bounded polytope with $\hat a \in \mathcal U$. Let $\lambda^*$ be the optimal value of the linear program
--
--   $$\max\ \lambda \quad \text{s.t.}\quad q = \lambda\hat q + (1-\lambda)e/N,\quad e'(s_k+t_k) \ge v_k,\quad s_{k,i} + t_{k,j} \le (u_k'a_j)\,q_i\ \ \forall i,j,k, \tag{15}$$
--
--   and write $q^\lambda = \lambda\hat q + (1-\lambda)e_N$. Then
--
--   1. $\Pi_{q^{\lambda^*}}(\mathcal A) \subseteq \mathcal U$;
--   2. for every $\lambda \in \mathbb R$ with $\Pi_{q^\lambda}(\mathcal A) \subseteq \mathcal U$, $\Pi_{q^\lambda}(\mathcal A) \subseteq \Pi_{q^{\lambda^*}}(\mathcal A)$;
--   3. if $N\hat q_{\min} < 1$, with $\hat q_{\min} = \min_i \hat q_i$, then $q^{\lambda^*} \in \hat\Delta^N$ if and only if $\lambda^* \le 1/(1 - N\hat q_{\min})$.
--
--   This is Theorem 4.5 of Bertsimas and Brown with the paper's hypothesis that $\mathcal U$ is a (bounded) polytope. The existing theorem RiskUncSets.InnerApprox.theorem_4_5 proves the same conclusion for every polyhedron of the form (14), bounded or not.
--
--   **Formalization Note** The optimal value of (15) is the hypothesis that $\lambda^*$ is the greatest feasible $\lambda$; maximality in the $\|\cdot\|_{\hat q,\mathcal A}$ sense is stated as set containment, as in the existing theorem.
-- source:
--   Bertsimas & Brown, Constructing uncertainty sets for robust linear optimization, Operations Research 57(6) (2009) 1483–1495, doi:10.1287/opre.1080.0646, p. 1493, Theorem 4.5, (14)–(16)

import Mathlib
import Definitions.Def_RiskUncSets_InnerApprox_Setting
open RiskUncSets.InnerApprox

theorem BertsimasBrown2009.thm4_5_bounded_polytope_faithful {N n m : ℕ} (hN : 0 < N)
    (qh : Fin N → ℝ) (hqh : qh ∈ symRestrictedSimplex N) (a : Fin N → Fin n → ℝ)
    (u : Fin m → Fin n → ℝ) (v : Fin m → ℝ)
    (hbdd : Bornology.IsBounded (polytope u v)) (hmean : sampleMean a ∈ polytope u v)
    (lamStar : ℝ) (hopt : IsGreatest {lam | LP15Feasible qh a u v lam} lamStar) :
    permutohull (mix qh lamStar) a ⊆ polytope u v ∧
    (∀ lam : ℝ, permutohull (mix qh lam) a ⊆ polytope u v →
      permutohull (mix qh lam) a ⊆ permutohull (mix qh lamStar) a) ∧
    ((N : ℝ) * (⨅ i, qh i) < 1 →
      (mix qh lamStar ∈ restrictedSimplex N ↔
        lamStar ≤ 1 / (1 - (N : ℝ) * ⨅ i, qh i))) := by sorry
