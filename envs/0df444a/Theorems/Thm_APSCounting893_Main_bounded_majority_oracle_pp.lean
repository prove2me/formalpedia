-- Prove2me | Theorems.Thm_APSCounting893_Main_bounded_majority_oracle_pp
-- name    : APSCounting893.Main.bounded_majority_oracle_pp
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T19:45:53.80094+00:00
-- url     : https://prove2.me/theorems/639ff426-43a1-488a-8e41-9ee6f7f2dc1f
-- title:
--   Bounded strict-majority oracle queries lie in PP
-- statement:
--   Let $A$ be any language of finite binary words and let $q(n)=a(n+1)^b$, where $a,b$ are fixed natural numbers. The language
--
--   $$\left\{x:2^{q(|x|)}<2\left|\left\{w\in\{0,1\}^{q(|x|)}:A(\langle x,w\rangle)\right\}\right|\right\}$$
--
--   belongs to $\mathrm{PP}^{A}$. The majority is strict, and the case of a zero-length random seed is included. The pairing is the fixed prefix-free word encoding used throughout this development.
--
--   The conclusion uses an actual finite oracle machine with one uniform polynomial time bound for every input and every seed. It provides the majority layer in uniform threshold-gate evaluation.
-- source:
--   Andrews, Garg and Schost, Hilbert’s Nullstellensatz is in the Counting Hierarchy, https://arxiv.org/abs/2602.17904, Lemma 6.3, pp.45–46 (one strict-majority oracle layer). Used in Agarwal, Hari, Pandey and Shukla, STOC 2027 submission #893, Theorem 6.4, pp.25–26, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf.

import Definitions.Def_APSCounting893_Main_OracleProofPrimitives
set_option autoImplicit false
open APSCounting893.Main

theorem APSCounting893.Main.bounded_majority_oracle_pp (A : Language) (a b : ℕ) :
    InOraclePP A (fun x =>
      2^polyBound a b x.length < 2*Set.ncard
        {w : Word | w.length=polyBound a b x.length ∧ A (pairWord x w)}) := by sorry
