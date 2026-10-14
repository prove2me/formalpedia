-- Prove2me | Theorems.Thm_CPDNetworks_Known_lemma_3
-- name    : CPDNetworks.Known.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:28.102701+00:00
-- url     : https://prove2.me/theorems/5f963af7-79d8-4db9-847e-1ffcb0856c93
-- title:
--   Lemma 3 — for any $\alpha\in(0,1)$ the type I error of test (10) is at most $\alpha$
-- statement:
--   Let $\epsilon\in(0,1/2]$ and let $C_\epsilon>0$ be a constant for which the conclusion (38) of Lemma 12 holds. Let $n\ge1$, $1\le\tau\le T-1$, $\omega_n\ge0$ and $\alpha\in(0,1)$. Consider the test that rejects when $\|Z_T(\tau)\|_{2\to2}>H_{\alpha,n}$ with
--   $$H_{\alpha,n}=2\sqrt2(1+\epsilon)\sqrt{\omega_n}+C_\epsilon\log(2n/\alpha).$$
--   Then its type I error over $\mathcal S_n(\omega_n)$ satisfies
--   $$\alpha(\psi^\tau_{n,T})=\sup_{(\Theta^0,\Pi)\in\mathcal S_n(\omega_n)}\mathbb P_{(\Theta^0,\Pi)}\big\{\|Z_T(\tau)\|_{2\to2}>H_{\alpha,n}\big\}\le\alpha.$$
--
--   This is the level half of Theorem 1.
--
--   **Formalization Note.** "$C_\epsilon$ is the constant of Lemma 12" is a hypothesis (the predicate stating (38) with constant $C_\epsilon$); Lemma 12 shows such a constant exists.
-- source:
--   Enikeeva and Klopp, Change-point detection in dynamic networks with missing links, arXiv:2106.14470v2, p. 30, Lemma 3 (test (10), threshold (11), p. 10)

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
import Definitions.Def_CPDNetworks_Known_Setting
open scoped Matrix
open HighDimProb.RandomMatrices

namespace CPDNetworks.Known

/-- Lemma 3, p. 30: with `C_ϵ` a constant of Lemma 12, the test (10) with threshold (11) has
type I error at most `α`. -/
theorem lemma_3 (ε Cε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hC : 0 < Cε)
    (hnoise : IsNoiseConst ε Cε)
    (n T τ : ℕ) (ω α : ℝ) (hn : 1 ≤ n) (hτ1 : 1 ≤ τ) (hτT : τ < T) (hω : 0 ≤ ω)
    (hα0 : 0 < α) (hα1 : α < 1) :
    CPDNetworks.Lower.typeI (n := n) (T := T) ω (testKnown τ (thrKnown ε Cε ω α n)) ≤ α := by sorry

end CPDNetworks.Known
