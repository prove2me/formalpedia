-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_initial_counter_generating_function
-- name    : CountingLLL.ContractedWalk.initial_counter_generating_function
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:16:09.933583+00:00
-- url     : https://prove2.me/theorems/ec364d4d-31f5-40d6-a13f-82df0187e756
-- title:
--   Generating function for the contracted walk’s final counter
-- statement:
--   Let an independent initial bit equal one with probability $u$. If it is zero, start the contracted walk at level one with counter one; if it is one, start at level three with counter two. Let $N$ be the final counter, incremented on each upward move. For $0\le u\le1$, $0\le\theta<1/3$ and $0\le z\le1$, its generating function satisfies $\mathbb E[z^{N-1}]=(1-u)G_\theta(z)+uzG_\theta(z)^3$. This is the paper’s suppressed-early-return contracted-walk model; its coupling to the full machine remains separate.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedGF
open MeasureTheory CountingLLL.ContractedWalk
open scoped ENNReal

theorem CountingLLL.ContractedWalk.initial_counter_generating_function (u θ z : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hθ0 : 0 ≤ θ) (hθ : θ < 1/3) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (∫ x : Bool × Tape, z ^ (if x.1 then 1 + upwardCount x.2 3 else upwardCount x.2 1)
      ∂((bitLaw (ENNReal.ofReal u)).prod (tapeLaw (ENNReal.ofReal θ)))) =
      (1-u)*generatingFunction θ z + u*z*(generatingFunction θ z)^3 := by sorry
