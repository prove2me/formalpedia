-- Prove2me | Theorems.Thm_ConsistentSubmodular_twoTypeInterpolation
-- name    : ConsistentSubmodular.twoTypeInterpolation
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:25:47.184443+00:00
-- url     : https://prove2.me/theorems/7c12e7fc-4864-4fab-830a-64dcf43013de
-- title:
--   Lemma B.3 — two-type interpolation
-- statement:
--   Let $f$ be a nonnegative monotone submodular function on $[n]$ and let $Q,A,B\subseteq[n]$. Define the two-type objective
--   $$H_Q(A,B;s)=s(1-s)f(Q)+(1-s)^2f(Q\cup A)+s^2f(Q\cup B)+s(1-s)f(Q\cup A\cup B),$$
--   and put $\lambda=f(Q)$, $a=f(Q\cup A)-\lambda$, $b=f(Q\cup B)-\lambda$, and the residual overlap $o=f(Q\cup A)+f(Q\cup B)-f(Q\cup A\cup B)-\lambda$. Then:
--
--   1. for every $s\in[0,1]$,
--   $$H_Q(A,B;s)=\lambda+(1-s)a+sb-s(1-s)\,o;$$
--   2. at the midpoint,
--   $$H_Q(A,B;1/2)\ \ge\ \lambda+\frac{a+b}{2}-\frac{\min(a,b)}{4};$$
--   3. for every real $W$ with $f(Q\cup A)\ge W$ and $f(Q\cup B)\ge W$, every $s\in[0,1]$ satisfies $H_Q(A,B;s)\ge\tfrac34W$.
--
--   Role: Appendix B.2.1, equations (23) and (24); the edge between two vertices of the simplex keeps value at least $3W/4$, the source of the factor $3/4$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/MainResults.lean#L137-L139 (`ConsistentSubmodular.twoTypeInterpolation`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open ConsistentSubmodular

theorem ConsistentSubmodular.twoTypeInterpolation : TwoTypeInterpolationGoal := by sorry
