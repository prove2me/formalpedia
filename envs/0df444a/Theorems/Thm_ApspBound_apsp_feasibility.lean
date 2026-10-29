-- Prove2me | Theorems.Thm_ApspBound_apsp_feasibility
-- name    : ApspBound.apsp_feasibility
-- status  : Proved
-- author  : @darkhipo
-- created : 2026-10-29T02:18:15.286885+00:00
-- url     : https://prove2.me/theorems/e0a441c2-5315-4dbc-bb15-8082b174f577
-- title:
--   Analytic feasibility certificate for the APSP exponent 2.9929479187094
-- statement:
--   Consider the aligned-cache reduction for All-Pairs Shortest Paths (APSP), whose cost accounting is organized into 47 inequalities spanning the geometric regimes of the reduction and the four cost phases (scalar stages $x\in\{0,u\}$ and cyclic stages $z\in\{0,v\}$). Each inequality has the form $\text{target} < \Phi(T,G,q_1)$, where $\Phi$ is affine in the entropic cost parameters $T$ (box/cache formation), $G$ (box gain) and $q_1$ (residual query exponent), and the target is either $0$ (a positivity or geometry condition) or the stage saving $\delta = 3 - 2.9929479187094$. This theorem is the closed analytic feasibility certificate: at the true real-logarithm parameters $T$, $G$, $q_1$—obtained from the binary-entropy analysis and pinned inside their certified rational enclosures by proved logarithm bounds—every one of the 47 cost inequalities holds with a common strictly positive slack $2\times 10^{-14}$; in particular the check family has exactly 47 members. Equivalently, each of the six cost categories of the written reduction saves strictly more than $\delta$ below cubic time, uniformly over every stage, certifying that the exponent $2.9929479187094$ (i.e. $3-\delta$) is analytically feasible for the reduction's cost model. The theorem is a certificate of these 47 cost inequalities at exact real-logarithm parameters; it does not by itself constitute a complete word-RAM algorithm for APSP.
-- source:
--   Joshua Wharton (QFEX), APSP aligned-cache exponent refinement (2026). Certificate adapted from shreshth-s/thin-matrix-results, commit 8a21eaae81599913dba562727e03a9b48c36a5b9. Packaged and independently verified by the BigO strike, 2026-10-28.

import Definitions.Def_ApspBound_Model

import Definitions.Def_ApspBound_Model

theorem ApspBound.apsp_feasibility :
    ApspBound.Numerical.checks.length = 47 ∧
    ∀ check ∈ ApspBound.Numerical.checks,
      (check.target : ℝ) + ApspBound.Analytic.uniformSlack <
        ApspBound.Analytic.evalReal check.expression := by sorry
