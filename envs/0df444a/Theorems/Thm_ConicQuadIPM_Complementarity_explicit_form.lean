-- Prove2me | Theorems.Thm_ConicQuadIPM_Complementarity_explicit_form
-- name    : ConicQuadIPM.Complementarity.explicit_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:33.247678+00:00
-- url     : https://prove2.me/theorems/15faef61-cc7e-4437-a804-61d8c06ec22d
-- title:
--   Appendix, p. 36 — XⁱSⁱeⁱ = SⁱXⁱeⁱ = 0 iff (xⁱ)ᵀsⁱ = 0 and (Tⁱxⁱ)₁(Tⁱsⁱ)₂:ₙ + (Tⁱsⁱ)₁(Tⁱxⁱ)₂:ₙ = 0
-- statement:
--   With the notation of Lemma 3.1, $X^i=\operatorname{mat}(T^ix^i)$, $S^i=\operatorname{mat}(T^is^i)$, the complementarity conditions of block $i$ can be stated explicitly: for arbitrary $x^i,s^i\in\mathbb R^{n^i}$,
--   $$
--   X^iS^ie^i=S^iX^ie^i=0
--   \iff
--   \begin{cases}
--   (x^i)^Ts^i=0,\\
--   (T^ix^i)_1(T^is^i)_{2:n}+(T^is^i)_1(T^ix^i)_{2:n}=0.
--   \end{cases}
--   $$
--
--   This unfolds the arrow-head product: the first component of $X^iS^ie^i$ is the inner product, the remaining components are the second line.
--
--   **Formalization Note.** The vector equation on the second line is stated componentwise for the indices $j\ge 1$ (0-based), i.e. the paper's components $2,\dots,n$. No cone membership is needed; `WellFormed` gives $(T^ix^i)^TT^is^i=(x^i)^Ts^i$.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, Appendix, proof of Lemma 3.1, p. 36 ("In explicit form the complementarity conditions can be stated as")

import Mathlib
import Definitions.Def_ConicQuadIPM_Complementarity_Setting

open Matrix

namespace ConicQuadIPM.Complementarity

theorem explicit_form {k : ℕ} (kind : Fin k → ConeKind) (n : Fin k → ℕ)
    (hwf : WellFormed kind n) (x s : (i : Fin k) → Fin (n i) → ℝ) (i : Fin k) :
    ((arrow (Tmat (kind i) (n i) *ᵥ x i) * arrow (Tmat (kind i) (n i) *ᵥ s i)) *ᵥ e1 = 0 ∧
      (arrow (Tmat (kind i) (n i) *ᵥ s i) * arrow (Tmat (kind i) (n i) *ᵥ x i)) *ᵥ e1 = 0) ↔
    (x i ⬝ᵥ s i = 0 ∧
      ∀ j : Fin (n i), 1 ≤ j.val →
        coord (Tmat (kind i) (n i) *ᵥ x i) 0 * (Tmat (kind i) (n i) *ᵥ s i) j +
          coord (Tmat (kind i) (n i) *ᵥ s i) 0 * (Tmat (kind i) (n i) *ᵥ x i) j = 0) := by sorry

end ConicQuadIPM.Complementarity
