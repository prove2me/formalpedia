-- Prove2me | Theorems.Thm_BatchTesting_PTAS_property_B
-- name    : BatchTesting.PTAS.property_B
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:48.17165+00:00
-- url     : https://prove2.me/theorems/d3930488-83a4-45a8-86fb-8ec1035b490f
-- title:
--   Property B, p. 19 (proof p. 22) — $N^{(m)}\ge N^{\diamond(m)}$ for every $0\le m\le M$
-- statement:
--   In the setting of Lemma 5 — an instance with $n\ge1$, $p_i\in[0,1]$, $c_i>0$, $\beta\ge0$, $0<\epsilon\le1$, a path $N^*$ over the nice-looking states, its bucketed subsequence $N^{\diamond(0)},\dots,N^{\diamond(M)}$ and the §4.5 sequence $N^{(0)},\dots,N^{(M)}$ —
--
--   $$N^{(m)}\ \ge\ N^{\diamond(m)}\qquad\text{for every }0\le m\le M.$$
--
--   The great-looking sequence is always ahead of the bucketed one, so its probabilities $P_0(N^{(m-1)})$ are at most $P_0(N^{\diamond(m-1)})$ and it ends at $N^{(\mathrm{all})}$.
-- source:
--   Segev & Shaposhnik, A Polynomial-Time Approximation Scheme for Sequential Batch Testing of Series Systems, SSRN preprint 3277805 (Nov. 2018), p. 19, §4.4, Property B (proof p. 22, §4.6)

import Mathlib
import Definitions.Def_BatchTesting_PTAS_Model

namespace BatchTesting.PTAS

theorem property_B {n : ℕ} (I : Instance n) (hI : I.Standing) (eps : ℝ) (h0 : 0 < eps) (h1 : eps ≤ 1)
    (πs : List (State I eps)) (hπs : IsPath I eps (FNice I eps) πs) :
    List.Forall₂ (fun Nd N => Nd ≤ N) (bucketed I eps πs) (greatSeq I eps (bucketed I eps πs)) := by sorry

end BatchTesting.PTAS
