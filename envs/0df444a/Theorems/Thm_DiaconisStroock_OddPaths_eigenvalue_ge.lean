-- Prove2me | Theorems.Thm_DiaconisStroock_OddPaths_eigenvalue_ge
-- name    : DiaconisStroock.OddPaths.eigenvalue_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:07:01.131379+00:00
-- url     : https://prove2.me/theorems/f8f1fb5a-8e06-4454-af0f-e2ad454afc5c
-- title:
--   §1C, proof of Proposition 2, p. 41 — every eigenvalue β of P satisfies β ≥ −1 + 2/ι
-- statement:
--   Let $P$ be an irreducible transition matrix on a finite set $X$, reversible with respect to its stationary distribution $\pi$, let $\Sigma$ be a system of odd closed paths and $\iota=\iota(\Sigma)$ the quantity (1.7). Then every real eigenvalue $\beta$ of $P$ (a real $\beta$ with $P\varphi=\beta\varphi$ for some nonzero real $\varphi$) satisfies
--
--   $$
--   \beta\ge-1+\frac{2}{\iota}.
--   $$
--
--   This is the sentence that closes the proof of Proposition 2: dividing the inequality $E(\varphi^2)\le\frac{\iota}{2}(E(\varphi^2)+\langle\varphi,P\varphi\rangle)$ by $E(\varphi^2)$ for an eigenfunction gives a lower bound on any eigenvalue of $P$.
--
--   **Formalization Note** Aperiodicity is not assumed, as in the previous milestone. Eigenvalues are real eigenvalues with real eigenfunctions; for a reversible chain all eigenvalues are of this kind.
-- source:
--   Diaconis and Stroock, Geometric bounds for eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), p. 41, §1C, end of the proof of Proposition 2, https://doi.org/10.1214/aoap/1177005980

import Mathlib
import Definitions.Def_mm_spectral
import Definitions.Def_DiaconisStroock_OddPaths_Iota
open MarkovMixing

namespace DiaconisStroock.OddPaths

theorem eigenvalue_ge {V : Type*} [Fintype V] [DecidableEq V] (P : Matrix V V ℝ)
    (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P) (π : V → ℝ) (hπ : IsStationary P π)
    (hrev : DetailedBalance P π) (S : V → List V) (hS : IsOddPathSystem P π S) :
    ∀ β : ℝ, IsEigenvalue P β → -1 + 2 / iota P π S ≤ β := by sorry

end DiaconisStroock.OddPaths
