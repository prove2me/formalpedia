-- Prove2me | Theorems.Thm_AssemblyCoord_Feedback_proposition_2_i
-- name    : AssemblyCoord.Feedback.proposition_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:40.981042+00:00
-- url     : https://prove2.me/theorems/1c490a01-377c-417b-b4b3-266085be05e4
-- title:
--   Proposition 2(i), p. 10 (PDF 10) — with N ≤ M − 1 feedback periods an SPSE exists and every SPSE has all contractors exert q̲/N in every period, project level q̲
-- statement:
--   Consider the $M$-contractor, $N$-period assembly coordination game with information feedback, started from zero effort, under the standing assumptions $1 \le M$, $1 \le N$, $0 \le \underline q < q^* < \bar q$, $p, \gamma, c > 0$. If the number of feedback periods satisfies $N \le M - 1$, then:
--
--   1. there is a subgame-perfect secure equilibrium (SPSE) in which every contractor exerts the minimum effort in every period,
--   $$q_{i,n} = \frac{\underline q}{N}, \qquad i = 1,\dots,M,\ n = 1,\dots,N;$$
--   2. every SPSE has this property along its path, and its project effort level is
--   $$q_{\min}(\hat{\mathbf q}_N) = \underline q.$$
--
--   This is the coordination-failure half of the paper's characterization: with too few feedback periods, the secure refinement of subgame perfection selects the worst outcome, even though higher project levels are supported by other equilibria.
--
--   **Formalization Note.** "There exists a unique SPSE in which all contractors exert the minimum effort" is stated as existence of such an SPSE together with "every SPSE exerts the minimum along its path". Uniqueness of the whole profile would be false, because Definition 2 does not constrain play off the equilibrium path. $N \le M - 1$ is written `P.N + 1 ≤ P.M`, and periods are 0-based (`pathHist σ n`). Part (ii) of Proposition 2, which concerns $N > M - 1$, is not formalized: it is false as printed (with $M = 2$, $N = 3$, $\underline q = 3$, $\bar q = 9$, $q^* = 7$, $\gamma = p = 1$, $c = 3/4$, a subgame-perfect equilibrium with path $(1,1), (1,1), (3,3)$ has project level $5$, and no SPSE reaches $q^* = 7$ although part (ii) predicts it at $N = N^* = 3$).
-- source:
--   Zhang, Shokoohyar, Qi & Katok, Coordination for assembly, author manuscript (10 July 2025) of MSOM doi:10.1287/msom.2023.0342, p. 10 (PDF 10), Proposition 2(i)

import Mathlib
import Definitions.Def_AssemblyCoord_Feedback_Model

namespace AssemblyCoord.Feedback

theorem proposition_2_i (P : Params) (hP : P.Standing) (hN : P.N + 1 ≤ P.M) :
    (∃ σ : Profile P.M, P.IsSPSE 0 σ ∧
        ∀ n, n < P.N → ∀ i : Fin P.M, σ i (pathHist σ n) = P.qlo / P.N) ∧
    (∀ σ : Profile P.M, P.IsSPSE 0 σ →
        (∀ n, n < P.N → ∀ i : Fin P.M, σ i (pathHist σ n) = P.qlo / P.N) ∧
        projectLevel (P.final 0 σ []) = P.qlo) := by sorry

end AssemblyCoord.Feedback
