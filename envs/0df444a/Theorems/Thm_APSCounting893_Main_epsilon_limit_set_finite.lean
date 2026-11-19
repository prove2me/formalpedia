-- Prove2me | Theorems.Thm_APSCounting893_Main_epsilon_limit_set_finite
-- name    : APSCounting893.Main.epsilon_limit_set_finite
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:33:37.159375+00:00
-- url     : https://prove2.me/theorems/9cc22da5-4e75-4dfe-a743-70994794fc0a
-- title:
--   The actual projective epsilon-limit set is finite
-- statement:
--   Let $F$ be a polynomial map with the stated homogenizing degree bounds, and form the associated homogeneous square system. Perturb equation $i$ by $\epsilon z_i^{d_i}$.
--
--   The set $Z_0^*$ of actual projective limits of bounded-ramification $\epsilon$-Puiseux solutions is finite:
--
--   $$|Z_0^*|<\infty.$$
--
--   A limit is represented by an integral series vector with at least one coordinate of valuation zero, followed by residue and projective normalization. The set retains points at infinity. This supplies the finiteness assertion used in the resultant factorization.
-- source:
--   Agarwal, Hari, Pandey and Shukla, Approximate Polynomial Satisfiability and Integral Closure Membership in the Counting Hierarchy, STOC 2027 submission #893, Section 5.1, pp. 20–21, Lemma 5.2 and Remark 5.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf. Andrews, Garg and Schost, Hilbert’s Nullstellensatz is in the Counting Hierarchy, arXiv:2602.17904, https://arxiv.org/pdf/2602.17904, Definition 4.5 and Lemma 4.6, pp. 25–26.

import Definitions.Def_APSCounting893_Main_Resultant
set_option autoImplicit false
open APSCounting893.Main

theorem APSCounting893.Main.epsilon_limit_set_finite
    (F : RawMap) (c alpha : Affine ℂ F.n)
    (degrees : Fin (F.n + (F.n+1)) → ℕ) (hdegrees : HomogenizingDegrees F c alpha degrees) :
    (epsilonLimitSet F c alpha degrees).Finite := by sorry
