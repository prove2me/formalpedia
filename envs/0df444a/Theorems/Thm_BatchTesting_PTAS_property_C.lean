-- Prove2me | Theorems.Thm_BatchTesting_PTAS_property_C
-- name    : BatchTesting.PTAS.property_C
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:44.559813+00:00
-- url     : https://prove2.me/theorems/ae0da369-185e-4558-97f3-90aeda6ce04d
-- title:
--   Property C, p. 19 (proof pp. 22–24) — per-step charging with factors $1+3\epsilon$ and $2\epsilon^2$
-- statement:
--   In the setting of Lemma 5 — an instance with $n\ge1$, $p_i\in[0,1]$, $c_i>0$, $\beta\ge0$, $0<\epsilon\le1$, a path $N^*$ over the nice-looking states, its bucketed subsequence $N^{\diamond}$ with actions $\Delta^{\diamond(m)}=N^{\diamond(m)}-N^{\diamond(m-1)}$, and the §4.5 actions $\Delta^{(m)}$ — for every $1\le m\le M$,
--
--   $$\sum_{r=0}^{R}\Delta^{(m)}_r(1+\epsilon)^r\ \le\ (1+3\epsilon)\sum_{r=0}^{R}\Delta^{\diamond(m)}_r(1+\epsilon)^r\ +\ 2\epsilon^2\sum_{m'=1}^{m-1}\sum_{r=0}^{R}\Delta^{\diamond(m')}_r(1+\epsilon)^r.$$
--
--   The testing cost of each great-looking step is at most $1+3\epsilon$ times that of the bucketed step plus a $2\epsilon^2$ share of everything tested before; combined with Lemmas 3 and 4 this gives the explicit factor of Theorem 3.
--
--   **Formalization Note.** $\Delta^{(m)}$ is the integer-valued action of §4.5 (the same object as in Lemma 5). The proof uses $1+\epsilon\le2$ (inequality (12), p. 24), covered by the hypothesis $\epsilon\le1$.
-- source:
--   Segev & Shaposhnik, A Polynomial-Time Approximation Scheme for Sequential Batch Testing of Series Systems, SSRN preprint 3277805 (Nov. 2018), p. 19, §4.4, Property C (proof pp. 22–24, inequalities (8)–(12))

import Mathlib
import Definitions.Def_BatchTesting_PTAS_Model

namespace BatchTesting.PTAS

theorem property_C {n : ℕ} (I : Instance n) (hI : I.Standing) (eps : ℝ) (h0 : 0 < eps) (h1 : eps ≤ 1)
    (πs : List (State I eps)) (hπs : IsPath I eps (FNice I eps) πs) :
    ∀ m, m + 1 < (bucketed I eps πs).length →
      ∑ r, (greatDeltaZ I eps ((greatSeq I eps (bucketed I eps πs)).getD m 0)
          ((bucketed I eps πs).getD (m + 1) 0) r : ℝ) * (1 + eps) ^ (r : ℕ) ≤
        (1 + 3 * eps) * ∑ r, ((((bucketed I eps πs).getD (m + 1) 0 -
            (bucketed I eps πs).getD m 0) r : ℕ) : ℝ) * (1 + eps) ^ (r : ℕ) +
        2 * eps ^ 2 * ∑ j ∈ Finset.range m, ∑ r, ((((bucketed I eps πs).getD (j + 1) 0 -
            (bucketed I eps πs).getD j 0) r : ℕ) : ℝ) * (1 + eps) ^ (r : ℕ) := by sorry

end BatchTesting.PTAS
