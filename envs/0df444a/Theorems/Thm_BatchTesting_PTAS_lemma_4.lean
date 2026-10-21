-- Prove2me | Theorems.Thm_BatchTesting_PTAS_lemma_4
-- name    : BatchTesting.PTAS.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:43.517831+00:00
-- url     : https://prove2.me/theorems/bb49042b-add0-4080-b3dd-f4aa57e27df8
-- title:
--   Lemma 4, pp. 18–19 — $\sum_{m'\ge m}P_0(N^{\diamond(m'-1)})\le\frac{(1+\epsilon)^2}{\epsilon}P_0(N^{\diamond(m-1)})$
-- statement:
--   Let $(p,c,\beta)$ be an instance with $n\ge1$, $p_i\in[0,1]$, $c_i>0$, $\beta\ge0$, let $0<\epsilon\le1$, let $N^{*}$ be a path of the dynamic program over $F$, and let $N^{\diamond(0)},\dots,N^{\diamond(M)}$ be its bucketed subsequence (§4.3). Then for every $1\le m\le M$,
--
--   $$\sum_{m'=m}^{M}P_0\big(N^{\diamond(m'-1)}\big)\ \le\ \frac{(1+\epsilon)^2}{\epsilon}\cdot P_0\big(N^{\diamond(m-1)}\big).$$
--
--   Since consecutive bucketed states lie in distinct buckets of geometrically decreasing probability, the tail sums of $P_0$ are geometric; this bounds the extra cost Property C charges to earlier steps.
--
--   **Formalization Note.** Optimality of $N^*$ is not used, so it is not assumed. Steps with $P_0=0$ form one extra last bucket.
-- source:
--   Segev & Shaposhnik, A Polynomial-Time Approximation Scheme for Sequential Batch Testing of Series Systems, SSRN preprint 3277805 (Nov. 2018), pp. 18–19, §4.3, Lemma 4

import Mathlib
import Definitions.Def_BatchTesting_PTAS_Model

namespace BatchTesting.PTAS

theorem lemma_4 {n : ℕ} (I : Instance n) (hI : I.Standing) (eps : ℝ) (h0 : 0 < eps) (h1 : eps ≤ 1)
    (πs : List (State I eps)) (hπs : IsPath I eps (F I eps) πs) :
    ∀ k, k + 1 < (bucketed I eps πs).length →
      ∑ j ∈ Finset.Ico k ((bucketed I eps πs).length - 1), P0 I eps ((bucketed I eps πs).getD j 0) ≤
        (1 + eps) ^ 2 / eps * P0 I eps ((bucketed I eps πs).getD k 0) := by sorry

end BatchTesting.PTAS
