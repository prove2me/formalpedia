-- Prove2me | Theorems.Thm_AssemblyCoord_Feedback_prop_2_step1_best_response
-- name    : AssemblyCoord.Feedback.prop_2_step1_best_response
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:39.066276+00:00
-- url     : https://prove2.me/theorems/c181c5e5-55e7-4ac0-a908-55121aff5e58
-- title:
--   Proof of Proposition 2, Step 1 (uniqueness), oa6 (PDF 38) — in an SPE, one contractor at q̲/N in every period forces all to q̲/N
-- statement:
--   In the $M$-contractor, $N$-period coordination game with information feedback started from zero effort, under the standing assumptions, let $\sigma$ be a subgame-perfect equilibrium and suppose some contractor $j$ exerts $\underline q/N$ in every period along $\sigma$'s path. Then every contractor exerts $\underline q/N$ in every period along that path:
--   $$q_{i,n} = \frac{\underline q}{N}, \qquad i = 1,\dots,M,\ n = 1,\dots,N.$$
--
--   This is the best-response step of the uniqueness argument in Proposition 2(i): once one contractor stays at the minimum, the project level is $\underline q$ and any extra effort by another contractor is wasted cost.
--
--   **Formalization Note.** Periods are 0-based (`pathHist σ n`). No bound relating $N$ and $M$ is needed.
-- source:
--   Zhang, Shokoohyar, Qi & Katok, Coordination for assembly, author manuscript (10 July 2025) of MSOM doi:10.1287/msom.2023.0342, p. oa6 (PDF 38), proof of Proposition 2, Step 1, uniqueness paragraph

import Mathlib
import Definitions.Def_AssemblyCoord_Feedback_Model

namespace AssemblyCoord.Feedback

theorem prop_2_step1_best_response (P : Params) (hP : P.Standing) (σ : Profile P.M)
    (hσ : P.IsSPE 0 σ) (j : Fin P.M)
    (hj : ∀ n, n < P.N → σ j (pathHist σ n) = P.qlo / P.N) :
    ∀ n, n < P.N → ∀ i : Fin P.M, σ i (pathHist σ n) = P.qlo / P.N := by sorry

end AssemblyCoord.Feedback
