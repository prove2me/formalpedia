-- Prove2me | Theorems.Thm_BatchTesting_PTAS_lemma_3
-- name    : BatchTesting.PTAS.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:09.695996+00:00
-- url     : https://prove2.me/theorems/c1b912ef-8da7-456a-b6f8-c266a11dcc48
-- title:
--   Lemma 3, p. 18 — the bucketed optimal nice path costs at most $(1+\epsilon)^2\cdot\mathrm{OPT}_F(N^{(\mathrm{none})})$
-- statement:
--   Let $(p,c,\beta)$ be an instance with $n\ge1$, $p_i\in[0,1]$, $c_i>0$, $\beta\ge0$, and let $0<\epsilon\le1$. Let $N^{*(0)}=0\to\cdots\to N^{*(T)}=N^{(\mathrm{all})}$ be an optimal path of the dynamic program over the nice-looking states. Partition its steps $t$ into buckets by $P_0(N^{*(t-1)})\in((1+\epsilon)^{-\ell},(1+\epsilon)^{-(\ell-1)}]$, merge the steps of each non-empty bucket into one action, and let $N^{\diamond(0)}=0,\dots,N^{\diamond(M)}=N^{(\mathrm{all})}$ be the resulting subsequence of states, with $\Delta^{\diamond(m)}=N^{\diamond(m)}-N^{\diamond(m-1)}$. Then for every path $\pi$ of the dynamic program over $F$,
--
--   $$\sum_{m=1}^{M}P_0(N^{\diamond(m-1)})\cdot C(\Delta^{\diamond(m)})\ \le\ (1+\epsilon)^2\cdot\mathrm{cost}(\pi),$$
--
--   that is, the bucketed solution costs at most $(1+\epsilon)^2\cdot\mathrm{OPT}_F(N^{(\mathrm{none})})$.
--
--   The bucketed solution has at most one step per power of $1+\epsilon$ in probability; Lemma 4 and Property C rely on that structure.
--
--   **Formalization Note.** Steps with $P_0(N^{*(t-1)})=0$, which the page's intervals miss when some $p_i=0$, form one extra last bucket; they contribute $0$ to both sides.
-- source:
--   Segev & Shaposhnik, A Polynomial-Time Approximation Scheme for Sequential Batch Testing of Series Systems, SSRN preprint 3277805 (Nov. 2018), p. 18, §4.3, Lemma 3 (bucketing pp. 17–18)

import Mathlib
import Definitions.Def_BatchTesting_PTAS_Model

namespace BatchTesting.PTAS

theorem lemma_3 {n : ℕ} (I : Instance n) (hI : I.Standing) (eps : ℝ) (h0 : 0 < eps) (h1 : eps ≤ 1)
    (πs : List (State I eps)) (hπs : IsOptPath I eps (FNice I eps) πs)
    (π : List (State I eps)) (hπ : IsPath I eps (F I eps) π) :
    pathCost I eps (bucketed I eps πs) ≤ (1 + eps) ^ 2 * pathCost I eps π := by sorry

end BatchTesting.PTAS
