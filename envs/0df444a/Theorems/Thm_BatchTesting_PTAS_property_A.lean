-- Prove2me | Theorems.Thm_BatchTesting_PTAS_property_A
-- name    : BatchTesting.PTAS.property_A
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:52.288242+00:00
-- url     : https://prove2.me/theorems/149161a8-eaab-4d5d-95f9-ea4ea20b8d28
-- title:
--   Property A, p. 19 (proof p. 22) — every state of the §4.5 sequence is great-looking
-- statement:
--   In the setting of Lemma 5 — an instance with $n\ge1$, $p_i\in[0,1]$, $c_i>0$, $\beta\ge0$, $0<\epsilon\le1$, a path $N^*$ of the dynamic program over the nice-looking states, its bucketed subsequence $N^{\diamond(0)},\dots,N^{\diamond(M)}$, and the §4.5 sequence $N^{(0)},\dots,N^{(M)}$ built from it —
--
--   $$N^{(0)},\dots,N^{(M)}\ \in\ F_{\mathrm{great}}.$$
--
--   So the §4.5 sequence is (after removing repeated states) a feasible solution of the dynamic program restricted to great-looking states, which is how Theorem 3 bounds $\mathrm{OPT}_{F_{\mathrm{great}}}$.
--
--   **Formalization Note.** The bound $\|\mu\|_1\le 3\kappa/\epsilon^2$ in the definition of great-looking needs $\epsilon\le1$ in the proof (p. 22: $2\kappa/\epsilon^2+\kappa\le3\kappa/\epsilon^2$); this is the reason for the mission-wide hypothesis.
-- source:
--   Segev & Shaposhnik, A Polynomial-Time Approximation Scheme for Sequential Batch Testing of Series Systems, SSRN preprint 3277805 (Nov. 2018), p. 19, §4.4, Property A (proof p. 22, §4.6)

import Mathlib
import Definitions.Def_BatchTesting_PTAS_Model

namespace BatchTesting.PTAS

theorem property_A {n : ℕ} (I : Instance n) (hI : I.Standing) (eps : ℝ) (h0 : 0 < eps) (h1 : eps ≤ 1)
    (πs : List (State I eps)) (hπs : IsPath I eps (FNice I eps) πs) :
    ∀ N ∈ greatSeq I eps (bucketed I eps πs), N ∈ FGreat I eps := by sorry

end BatchTesting.PTAS
