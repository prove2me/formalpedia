-- Prove2me | Theorems.Thm_DoubleAuctionEff_Repeated_lemma_2
-- name    : DoubleAuctionEff.Repeated.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:56.627572+00:00
-- url     : https://prove2.me/theorems/866ee755-7134-40a0-bb88-8b5230e1c4f7
-- title:
--   Lemma 2, p. 10 — under Assumption 1 the indifference price D_i is concave and usc, D_i(0) = 0, and D_i(x_i + rg) = D_i(x_i) + r
-- statement:
--   Let $u:\mathbb R^J\to[-\infty,+\infty]$ satisfy Assumption 1 (upper semicontinuous, concave, strictly increasing along the numeraire $g$ on its domain), let $x^0\in\operatorname{dom}u$, and let
--   $$D(x)=\sup\{r\in\mathbb R\mid u(x^0+x-rg)\ge u(x^0)\}$$
--   be the indifference price. Then $D$ is concave and upper semicontinuous, $D(0)=0$, and
--   $$D(x+rg)=D(x)+r\qquad\text{for all }x\in\operatorname{dom}D,\ r\in\mathbb R.$$
--
--   This is the basic regularity of the bids the agents submit: it makes (P) a concave maximization problem and shows that the numeraire is priced at its face value.
--
--   **Formalization Note** The hypothesis $x^0\in\operatorname{dom}u$ is added: if $u(x^0)=-\infty$ every $r$ qualifies, $D\equiv+\infty$ and $D(0)\ne0$. The paper treats this as implicit.
-- source:
--   T. Pennanen, Efficient allocations in double auction markets, arXiv:2001.02071v2, p. 10, Lemma 2 (with (1), p. 8, and Assumption 1, p. 8)

import Mathlib
import Definitions.Def_DoubleAuctionEff_Repeated_Model

namespace DoubleAuctionEff.Repeated
theorem lemma_2 {J : Type*} [Fintype J] (u : (J → ℝ) → EReal) (g x0 : J → ℝ)
    (h1 : Assumption1 u g) (hx0 : x0 ∈ dom u) :
    IsConcaveE (indiffPrice u g x0) ∧ UpperSemicontinuous (indiffPrice u g x0) ∧
      indiffPrice u g x0 0 = 0 ∧
      ∀ y ∈ dom (indiffPrice u g x0), ∀ r : ℝ,
        indiffPrice u g x0 (y + r • g) = indiffPrice u g x0 y + (r : EReal) := by sorry
end DoubleAuctionEff.Repeated
