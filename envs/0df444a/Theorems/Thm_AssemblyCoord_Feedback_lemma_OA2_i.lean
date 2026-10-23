-- Prove2me | Theorems.Thm_AssemblyCoord_Feedback_lemma_OA2_i
-- name    : AssemblyCoord.Feedback.lemma_OA2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:33.676199+00:00
-- url     : https://prove2.me/theorems/e431a965-c812-47af-8bed-dbb995237f18
-- title:
--   Lemma OA2(i), oa5 (PDF 37) — with N ≤ M − 1 and at least N + 1 contractors tied at the lowest initial effort, some SPE has everyone exert q̲/N in every period
-- statement:
--   Consider the $M$-contractor, $N$-period coordination game with information feedback, under the standing assumptions, started from an arbitrary initial effort vector $\hat{\mathbf q}_0 = (\hat q_{1,0},\dots,\hat q_{M,0})$. Suppose that
--   1. $N \le M - 1$, and
--   2. at least $N+1$ contractors share the lowest initial effort level: there is a set $S$ of contractors with $|S| \ge N+1$ and $\hat q_{i,0} \le \hat q_{j,0}$ for all $i \in S$ and all $j$.
--
--   Then there is a subgame-perfect equilibrium $\sigma$ along whose path every contractor exerts the minimum per-period effort in every period:
--   $$q_{i,n} = \frac{\underline q}{N}, \qquad i = 1,\dots,M,\ n = 1,\dots,N.$$
--
--   This is the existence half of Proposition 2(i): it supplies an SPE with the all-minimum outcome, which is then shown to be secure.
--
--   **Formalization Note.** The hypothesis is the lemma's prose ("at least $N+1$ contractors have equal lowest initial effort level"), not the display (26), which prints all $M$ levels equal; the prose is the weaker hypothesis. "All contractors exert at the lower boundary in each period is an SPE strategy" is read as "some SPE has this path": the profile that plays $\underline q/N$ after every history is not an SPE when $\gamma p > c$, since a contractor left strictly behind with one period to go gains by catching up. $N \le M-1$ is written `P.N + 1 ≤ P.M`.
-- source:
--   Zhang, Shokoohyar, Qi & Katok, Coordination for assembly, author manuscript (10 July 2025) of MSOM doi:10.1287/msom.2023.0342, p. oa5 (PDF 37), Lemma OA2(i), (26)

import Mathlib
import Definitions.Def_AssemblyCoord_Feedback_Model

namespace AssemblyCoord.Feedback

theorem lemma_OA2_i (P : Params) (hP : P.Standing) (hN : P.N + 1 ≤ P.M)
    (q0 : Fin P.M → ℝ)
    (htie : ∃ S : Finset (Fin P.M), P.N + 1 ≤ S.card ∧ ∀ i ∈ S, ∀ j, q0 i ≤ q0 j) :
    ∃ σ : Profile P.M, P.IsSPE q0 σ ∧
      ∀ n, n < P.N → ∀ i : Fin P.M, σ i (pathHist σ n) = P.qlo / P.N := by sorry

end AssemblyCoord.Feedback
