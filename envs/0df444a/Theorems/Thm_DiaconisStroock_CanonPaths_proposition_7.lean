-- Prove2me | Theorems.Thm_DiaconisStroock_CanonPaths_proposition_7
-- name    : DiaconisStroock.CanonPaths.proposition_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:07:46.266581+00:00
-- url     : https://prove2.me/theorems/ac1ca0df-5149-4f12-be4a-089746537ba5
-- title:
--   Proposition 7: β₁ ≤ 1 − 1/(8η²)
-- statement:
--   Let $P$ be a reversible irreducible Markov chain on a finite set of at least two states, with stationary distribution $\pi$. Choose a positive-flow walk $\gamma_{xy}$ for every distinct ordered pair $x,y$ and define its directed-edge congestion $\eta$ by (3.2). If $\beta_1$ is the second largest eigenvalue of $P$, then
--
--   $$
--   \beta_1\leq 1-\frac{1}{8\eta^2}.
--   $$
--
--   The bound estimates the second eigenvalue using a geometric load imposed by the chosen walks. It is the central result of this mission.
--
--   **Formalization Note** The at-least-two-states condition makes $\beta_1$ well defined. The Lean walk system only constrains distinct endpoints; equal-endpoint choices are ignored by $\eta$. The theorem assumes neither the intermediate bottleneck bound nor Cheeger's inequality.
-- source:
--   Diaconis and Stroock, Geometric bounds for eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), p. 54, Proposition 7 and (3.2); https://doi.org/10.1214/aoap/1177005980

import Mathlib
import Definitions.Def_mm_spectral
import Definitions.Def_DiaconisStroock_CanonPaths_Eta

namespace DiaconisStroock.CanonPaths

open MarkovMixing

/-- Proposition 7, p. 54: the second eigenvalue is bounded by the congestion of any
system of canonical walks on an irreducible reversible chain. -/
theorem proposition_7 {V : Type*} [Fintype V] [DecidableEq V]
    (hV : 2 ≤ Fintype.card V) (P : Matrix V V ℝ) (hP : IsStochastic P)
    (hirr : MarkovMixing.Irreducible P) (π : V → ℝ) (hπ : IsStationary P π)
    (hrev : DetailedBalance P π) (Γ : V → V → List V)
    (hΓ : IsWalkSystem P π Γ) :
    lambdaTwo P ≤ 1 - 1 / (8 * eta P π Γ ^ 2) := by sorry

end DiaconisStroock.CanonPaths
