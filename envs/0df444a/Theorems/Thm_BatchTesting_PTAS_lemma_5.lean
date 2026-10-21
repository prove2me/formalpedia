-- Prove2me | Theorems.Thm_BatchTesting_PTAS_lemma_5
-- name    : BatchTesting.PTAS.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:46.15269+00:00
-- url     : https://prove2.me/theorems/dc0e8d17-034a-4125-b863-38f3b7b93bf5
-- title:
--   Lemma 5, p. 21 — the actions $\Delta^{(m)}$ of the §4.5 construction are non-negative
-- statement:
--   Let $(p,c,\beta)$ be an instance with $n\ge1$, $p_i\in[0,1]$, $c_i>0$, $\beta\ge0$, let $0<\epsilon\le1$, let $N^*$ be a path of the dynamic program over the nice-looking states, and let $N^{\diamond(0)},\dots,N^{\diamond(M)}$ be its bucketed subsequence. Let $N^{(0)}=0,\dots,N^{(M)}$ be the §4.5 sequence: with $\rho_m=\lceil\log_{1+\epsilon}\sum_{r\le\psi(N^{\diamond(m)})}N^{\diamond(m)}_r(1+\epsilon)^r\rceil$ and $\mu^{(m)}_r$ the least integer with $\mu^{(m)}_r(\epsilon^2/\kappa)P_2[(1+\epsilon)^{\rho_m}]\ge N^{\diamond(m)}_r(1+\epsilon)^r$, the integer vector
--
--   $$\Delta^{(m)}_r=\begin{cases}|C_r|-N^{(m-1)}_r,& r\le\psi(N^{\diamond(m)})-\kappa,\\ \min\Big\{\Big\lfloor\frac{\mu^{(m)}_r(\epsilon^2/\kappa)P_2[(1+\epsilon)^{\rho_m}]}{(1+\epsilon)^r}\Big\rfloor,|C_r|\Big\}-N^{(m-1)}_r,& \psi(N^{\diamond(m)})-\kappa<r\le\psi(N^{\diamond(m)}),\\ 0,& r>\psi(N^{\diamond(m)}),\end{cases}$$
--
--   and $N^{(m)}=N^{(m-1)}+\Delta^{(m)}$. Then $\Delta^{(m)}\ge0$ for every $1\le m\le M$.
--
--   The roundings in $\rho_m$ and $\mu^{(m)}$ go in opposite directions; the lemma says they never force a class count to decrease, so the construction is a sequence of feasible actions.
--
--   **Formalization Note.** $\Delta^{(m)}$ is computed in $\mathbb Z$, so the claim is not automatic. The page's proof has a typo in its first displayed line (p. 21); the statement is unaffected. The page takes an optimal nice path; optimality is not used, so it is not assumed.
-- source:
--   Segev & Shaposhnik, A Polynomial-Time Approximation Scheme for Sequential Batch Testing of Series Systems, SSRN preprint 3277805 (Nov. 2018), p. 21, §4.5, Lemma 5 (construction p. 20, eqs. (4)–(5))

import Mathlib
import Definitions.Def_BatchTesting_PTAS_Model

namespace BatchTesting.PTAS

theorem lemma_5 {n : ℕ} (I : Instance n) (hI : I.Standing) (eps : ℝ) (h0 : 0 < eps) (h1 : eps ≤ 1)
    (πs : List (State I eps)) (hπs : IsPath I eps (FNice I eps) πs) :
    ∀ m, m + 1 < (bucketed I eps πs).length → ∀ r,
      0 ≤ greatDeltaZ I eps ((greatSeq I eps (bucketed I eps πs)).getD m 0)
        ((bucketed I eps πs).getD (m + 1) 0) r := by sorry

end BatchTesting.PTAS
