-- Prove2me | Theorems.Thm_DiaconisStroock_Poincare_sq_sub_le_qLength_mul
-- name    : DiaconisStroock.Poincare.sq_sub_le_qLength_mul
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:02:40.227485+00:00
-- url     : https://prove2.me/theorems/9d823021-1806-4a8f-a564-f02513f0827a
-- title:
--   §1B, proof of Proposition 1 — path Cauchy–Schwarz inequality
-- statement:
--   For a walk $\gamma$ from $x$ to $y$ along positive-$Q$ edges of a finite stochastic chain, with $Q(z,w)=\pi(z)P(z,w)$, any real function $\phi$ satisfies
--
--   $$
--   (\phi(y)-\phi(x))^2\le |\gamma|_Q
--     \sum_{e\in\gamma}Q(e)\bigl(\phi(e^+)-\phi(e^-)\bigr)^2.
--   $$
--
--   This is the per-path Cauchy–Schwarz inequality displayed in the proof of Proposition 1.
--
--   **Formalization Note** The inequality holds for walks even when an edge repeats; repeated traversals are counted in both sums. The full path system later requires edge-simple paths.
-- source:
--   Diaconis and Stroock, Geometric bounds for eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), p. 38, §1B, proof of Proposition 1, second and third display lines, https://doi.org/10.1214/aoap/1177005980

import Mathlib
import Definitions.Def_DiaconisStroock_Poincare_Paths

namespace DiaconisStroock.Poincare

open MarkovMixing

/-- The per-path Cauchy–Schwarz step in the proof of Proposition 1, p. 38. -/
theorem sq_sub_le_qLength_mul {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (π : V → ℝ)
    (x y : V) (p : List V) (hp : IsWalk P π x y p) (φ : V → ℝ) :
    (φ y - φ x) ^ 2 ≤ qLength P π p *
      ((pathEdges p).map fun e =>
        edgeMeasure P π e.1 e.2 * (φ e.2 - φ e.1) ^ 2).sum := by sorry

end DiaconisStroock.Poincare
