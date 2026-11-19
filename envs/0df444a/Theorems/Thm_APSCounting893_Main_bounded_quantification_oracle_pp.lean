-- Prove2me | Theorems.Thm_APSCounting893_Main_bounded_quantification_oracle_pp
-- name    : APSCounting893.Main.bounded_quantification_oracle_pp
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T07:17:25.944241+00:00
-- url     : https://prove2.me/theorems/9e893df2-aef5-4e85-98e7-4fda778c8de7
-- title:
--   Bounded word quantification with one majority-oracle level
-- statement:
--   Let $A$ be a language and fix natural numbers $a,b$ with $a>0$. Use the delimited pairing code $\langle x,y\rangle$ and the common length bound $p(n)=a(n+1)^b$. Both bounded quantifier languages satisfy
--
--   $$\{x:\exists y\in\{0,1\}^{p(|x|)},\ \langle x,y\rangle\in A\}\in PP^A,$$
--   $$\{x:\forall y\in\{0,1\}^{p(|x|)},\ \langle x,y\rangle\in A\}\in PP^A.$$
--
--   The machines have finite control and use strict majority, including the tie cases. This is the bounded-quantifier step used in Lemma 6.5's Counting Hierarchy argument.
-- source:
--   Auxiliary finite-machine proof component for Agarwal, Hari, Pandey, Shukla, STOC 2027 submission #893, Lemma 6.5, p. 26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_OracleProofPrimitives

set_option autoImplicit false

theorem APSCounting893.Main.bounded_quantification_oracle_pp
    (A : APSCounting893.Main.Language) (a b : ℕ) (ha : 0 < a) :
    APSCounting893.Main.InOraclePP A (fun x => ∃ y : APSCounting893.Main.Word,
      y.length = APSCounting893.Main.polyBound a b x.length ∧ A (APSCounting893.Main.pairWord x y)) ∧
    APSCounting893.Main.InOraclePP A (fun x => ∀ y : APSCounting893.Main.Word,
      y.length = APSCounting893.Main.polyBound a b x.length → A (APSCounting893.Main.pairWord x y)) := by sorry
