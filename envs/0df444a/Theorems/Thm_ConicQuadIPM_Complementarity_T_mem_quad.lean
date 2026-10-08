-- Prove2me | Theorems.Thm_ConicQuadIPM_Complementarity_T_mem_quad
-- name    : ConicQuadIPM.Complementarity.T_mem_quad
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:27.94071+00:00
-- url     : https://prove2.me/theorems/fba26629-0c2d-4631-a463-3462e8e5c7c3
-- title:
--   Appendix, proof of Lemma 3.1, p. 36 — x ∈ K implies Tⁱxⁱ ∈ Kq for every cone i
-- statement:
--   Let $K=K^1\times\dots\times K^k$ be a product of cones of the types $\mathbb R_+$, $K^q$, $K^r$, and let $T^i$ be the matrices of Definition 3.2. If $x\in K$, then for every $i$
--   $$
--   T^ix^i\in K^q .
--   $$
--
--   For $\mathbb R_+$ and $K^q$ this is immediate ($T^i=I$); for $K^r$ it is the reverse direction of the p. 9 equivalence. It reduces every cone of the product to a quadratic cone in the proof of Lemma 3.1.
--
--   **Formalization Note.** For a block of type $\mathbb R_+$ (dimension 1), $K^q$ of dimension 1 is $\{x_1\ge0\}$. The block dimensions are the disclosed hypothesis `WellFormed`.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, Appendix, proof of Lemma 3.1, p. 36 ("Note that Tⁱxⁱ, Tⁱsⁱ ∈ K^q")

import Mathlib
import Definitions.Def_ConicQuadIPM_Complementarity_Setting

open Matrix

namespace ConicQuadIPM.Complementarity

theorem T_mem_quad {k : ℕ} (kind : Fin k → ConeKind) (n : Fin k → ℕ)
    (hwf : WellFormed kind n) (x : (i : Fin k) → Fin (n i) → ℝ) (hx : inK kind x) :
    ∀ i, inQuad (Tmat (kind i) (n i) *ᵥ x i) := by sorry

end ConicQuadIPM.Complementarity
