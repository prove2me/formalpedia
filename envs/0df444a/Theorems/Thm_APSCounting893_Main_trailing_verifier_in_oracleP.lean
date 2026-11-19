-- Prove2me | Theorems.Thm_APSCounting893_Main_trailing_verifier_in_oracleP
-- name    : APSCounting893.Main.trailing_verifier_in_oracleP
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T07:17:53.281698+00:00
-- url     : https://prove2.me/theorems/db40eabb-6ab9-41fa-884e-b7ae7cd2b19c
-- title:
--   Polynomial oracle verifier for lexicographic trailing coefficients
-- statement:
--   Fix a number $k$ of parameter variables and a family $\rho$ of represented rational coefficients. Let $B_\rho$ be the language of individual coefficient-bit queries. The delimited trailing-test verifier satisfies
--
--   $$V_\rho\in P^{B_\rho}.$$
--
--   Its input contains a word $x$, a candidate full exponent $a=(\alpha,s)$ with a numerator-bit index $q_A$, and a universal payload $(e,q_E,q_F)$. It accepts exactly when the candidate bit is one, either $e_{<k}$ is not lexicographically earlier than $\alpha$ or its queried bit is zero, and the queried bit at $(\alpha,0)$ is zero. Invalid pair or candidate encodings reject; an invalid universal payload is accepted after the candidate-bit check.
--
--   This verifier is the inner predicate of Lemma 6.5. No degree or coefficient-height promise is needed for the verifier's polynomial runtime.
-- source:
--   Auxiliary finite-machine proof component for Agarwal, Hari, Pandey, Shukla, STOC 2027 submission #893, Lemma 6.5, p. 26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_OracleProofPrimitives

set_option autoImplicit false

theorem APSCounting893.Main.trailing_verifier_in_oracleP (k : ℕ)
    (rho : APSCounting893.Main.CoefficientRepresentation k) :
    APSCounting893.Main.InOracleP (APSCounting893.Main.CoefficientBitLanguage rho)
      (APSCounting893.Main.BaseTrailingLanguage rho) := by sorry
