-- Prove2me | Theorems.Thm_DataGrowth_BGP_lemma_A_1
-- name    : DataGrowth.BGP.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:16.851357+00:00
-- url     : https://prove2.me/theorems/eea1fd4c-1fe6-4bb3-93c8-df3d3cc17c93
-- title:
--   Lemma A.1, PDF p. 24 — labor shares with constant growth rates summing to one have growth rate zero
-- statement:
--   Let $a,b$ be functions of time that are positive on $t>0$ with constant growth rates $g_a,g_b$, i.e. $\dot a=g_a a$ and $\dot b=g_b b$ for $t>0$, and suppose $a(t)+b(t)=1$ for all $t>0$. Then
--   $$
--   g_a=g_b=0,
--   $$
--   and $a$ and $b$ are constant on $t>0$.
--
--   This is Lemma A.1 of the paper ("In BGP, the ratios of labor employed in production sector and R&D sector both converge to constants, thus their growth rates are both zero"), applied to $(l_E,l_R)$ in the decentralized economy and in the planner's economy. It is used throughout the proofs of Propositions 1 and 3.
--
--   **Formalization Note** The lemma is stated abstractly, exactly in the form its proof uses; "converge to constants" is rendered as "are constant for $t>0$".
-- source:
--   Cong, Xie, Zhang, Knowledge Accumulation, Privacy, and Growth in a Data Economy, arXiv:2109.10028v1, p. 24 (Online Appendix p. 1), Lemma A.1

import Mathlib
import Definitions.Def_DataGrowth_BGP_Params

namespace DataGrowth.BGP

/-- Cong, Xie, Zhang, *Knowledge Accumulation, Privacy, and Growth in a Data Economy*, arXiv:2109.10028v1, PDF p. 24 (Online Appendix p. 1), Lemma A.1: in BGP the labor shares of the
production and R&D sectors are constant, so their growth rates are zero.

Stated abstractly, as the proof uses it: two positive functions a, b with constant growth rates
g_a, g_b and a(t) + b(t) = 1 for every t > 0 have g_a = g_b = 0 and are constant on t > 0. It
applies to (l_E, l_R) of the decentralized economy ((17), p. 7, with l_E + l_R = 1) and of the
planner's economy ((27), p. 11).

Formalization Note: "converge to constants" is rendered as "are constant on t > 0", which is what
a constant growth rate of zero gives; labor-market clearing is the equality l_E + l_R = 1 used in
the proof. -/
theorem lemma_A_1 (a b : ℝ → ℝ) (ga gb : ℝ) (ha : HasConstGrowth a ga)
    (hb : HasConstGrowth b gb) (hsum : ∀ t : ℝ, 0 < t → a t + b t = 1) :
    ga = 0 ∧ gb = 0 ∧ ∃ a0 b0 : ℝ, ∀ t : ℝ, 0 < t → a t = a0 ∧ b t = b0 := by sorry

end DataGrowth.BGP
