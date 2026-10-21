-- Prove2me | Theorems.Thm_BatchTesting_PTAS_lemma_1
-- name    : BatchTesting.PTAS.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:40.613858+00:00
-- url     : https://prove2.me/theorems/cfa6e2d4-a015-4585-9ec8-17ec00a71a54
-- title:
--   Lemma 1, p. 13 — the §3.4 sequence dominates the path: $N^{(t)}\ge N^{*(t)}$
-- statement:
--   Let $(p,c,\beta)$ be an instance with $n\ge1$, $p_i\in[0,1]$, $c_i>0$, $\beta\ge0$, let $0<\epsilon\le1$, and let $N^{*(0)}=0\to\cdots\to N^{*(T)}=N^{(\mathrm{all})}$ be a path of the dynamic program over $F$. Let $N^{(0)}=0,N^{(1)},\dots,N^{(T)}$ be the sequence of §3.4: with $\bar\Delta^{(t)}=[N^{*(t)}-N^{(t-1)}]^+$, the action $\Delta^{(t)}$ copies $\bar\Delta^{(t)}$ on the $\kappa$ classes ending at $\psi(\bar\Delta^{(t)})$, exhausts every class $r\le\psi(\bar\Delta^{(t)})-\kappa$, and leaves the classes above $\psi(\bar\Delta^{(t)})$ alone; $N^{(t)}=N^{(t-1)}+\Delta^{(t)}$. Then
--
--   $$N^{(t)}\ \ge\ N^{*(t)}\qquad\text{for every }0\le t\le T.$$
--
--   Together with Lemma 2, this shows that the nice-looking sequence costs at most $1+\epsilon$ times the original path (Theorem 2).
--
--   **Formalization Note.** The sequence may repeat a state (a zero action), as on the page.
-- source:
--   Segev & Shaposhnik, A Polynomial-Time Approximation Scheme for Sequential Batch Testing of Series Systems, SSRN preprint 3277805 (Nov. 2018), p. 13, §3.4, Lemma 1

import Mathlib
import Definitions.Def_BatchTesting_PTAS_Model

namespace BatchTesting.PTAS

theorem lemma_1 {n : ℕ} (I : Instance n) (hI : I.Standing) (eps : ℝ) (h0 : 0 < eps) (h1 : eps ≤ 1)
    (πs : List (State I eps)) (hπs : IsPath I eps (F I eps) πs) :
    List.Forall₂ (fun Nstar N => Nstar ≤ N) πs (niceSeq I eps πs) := by sorry

end BatchTesting.PTAS
