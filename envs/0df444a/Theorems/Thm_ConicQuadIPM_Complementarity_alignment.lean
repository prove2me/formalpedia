-- Prove2me | Theorems.Thm_ConicQuadIPM_Complementarity_alignment
-- name    : ConicQuadIPM.Complementarity.alignment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:57.3669+00:00
-- url     : https://prove2.me/theorems/b4e9bf29-3e21-4cad-95ce-ccd5b4d66d2b
-- title:
--   Appendix, p. 37 — (Tⁱxⁱ)₂:ₙ = α(Tⁱsⁱ)₂:ₙ with α = −(Tⁱxⁱ)₁/(Tⁱsⁱ)₁, so (20) holds for block i
-- statement:
--   Let $K=K^1\times\dots\times K^k$ be as in §3, $x,s\in K$, and let $i$ be a block with $(x^i)^Ts^i=0$, $(T^ix^i)_1\ne0$ and $(T^is^i)_1\ne0$. Then
--   $$
--   (T^ix^i)_{2:n}=\alpha\,(T^is^i)_{2:n},\qquad \alpha=-\frac{(T^ix^i)_1}{(T^is^i)_1},
--   $$
--   and consequently the complementarity conditions (20) hold for block $i$:
--   $$
--   X^iS^ie^i=S^iX^ie^i=0,\qquad X^i=\operatorname{mat}(T^ix^i),\ S^i=\operatorname{mat}(T^is^i).
--   $$
--
--   This is the last step of the proof of Lemma 3.1: in a block where neither leading coordinate vanishes, complementarity forces the tails of $T^ix^i$ and $T^is^i$ to be anti-parallel with the stated ratio.
--
--   **Formalization Note.** The page derives $(x^i)^Ts^i=0$ from $x^Ts=0$ and the chain; here the block condition $(x^i)^Ts^i=0$ is the hypothesis, which is weaker. The vector identity is stated componentwise for the indices $j\ge1$ (0-based). Block dimensions (`WellFormed`) are a disclosed hypothesis.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, Appendix, proof of Lemma 3.1, p. 37

import Mathlib
import Definitions.Def_ConicQuadIPM_Complementarity_Setting

open Matrix

namespace ConicQuadIPM.Complementarity

theorem alignment {k : ℕ} (kind : Fin k → ConeKind) (n : Fin k → ℕ)
    (hwf : WellFormed kind n) (x s : (i : Fin k) → Fin (n i) → ℝ)
    (hx : inK kind x) (hs : inK kind s) (i : Fin k) (hcomp : x i ⬝ᵥ s i = 0)
    (hx1 : coord (Tmat (kind i) (n i) *ᵥ x i) 0 ≠ 0)
    (hs1 : coord (Tmat (kind i) (n i) *ᵥ s i) 0 ≠ 0) :
    (∀ j : Fin (n i), 1 ≤ j.val →
      (Tmat (kind i) (n i) *ᵥ x i) j =
        -(coord (Tmat (kind i) (n i) *ᵥ x i) 0 / coord (Tmat (kind i) (n i) *ᵥ s i) 0) *
          (Tmat (kind i) (n i) *ᵥ s i) j) ∧
    (arrow (Tmat (kind i) (n i) *ᵥ x i) * arrow (Tmat (kind i) (n i) *ᵥ s i)) *ᵥ e1 = 0 ∧
    (arrow (Tmat (kind i) (n i) *ᵥ s i) * arrow (Tmat (kind i) (n i) *ᵥ x i)) *ᵥ e1 = 0 := by sorry

end ConicQuadIPM.Complementarity
