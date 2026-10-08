-- Prove2me | Theorems.Thm_AffinePSD_InfDiv_lemma_6_2
-- name    : AffinePSD.InfDiv.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:37.745764+00:00
-- url     : https://prove2.me/theorems/4ca1c7ec-7afd-4f3c-9b5f-7470867bf357
-- title:
--   Lemma 6.2 — a measurable, strictly positive solution of $h(x+y)=h(x)h(y)$ on $S_d^+$ is $e^{-\langle c,x\rangle}$
-- statement:
--   Let $h:S_d^+\to\mathbb R_+$ be measurable and strictly positive, and let it satisfy Cauchy's exponential equation
--   $$h(x+y)=h(x)h(y),\qquad x,y\in S_d^+.\qquad(6.5)$$
--   Then there is $c\in S_d$ with
--   $$h(x)=e^{-\langle c,x\rangle}\qquad\text{for all }x\in S_d^+.$$
--   If moreover $h\le1$, then $c\in S_d^+$.
--
--   This is the main ingredient of Lemma 6.4. A Laplace functional that is multiplicative in the initial state must be exponential-affine in it.
--
--   **Formalization Note** The symmetric $c$ is unique, so the conclusion "$c\in S_d^+$" is stated for that same $c$.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), §6.3, Lemma 6.2, (6.5), p. 54

import Mathlib
import Definitions.Def_AffinePSD_InfDiv_Cone

namespace AffinePSD.InfDiv

/-- Lemma 6.2 (arXiv:0910.0137v3, §6.3, p. 54). Let `h : S_d^+ → ℝ_+` be measurable, strictly
positive, and satisfy Cauchy's exponential equation `h(x + y) = h(x) h(y)` (6.5). Then
`h(x) = e^{−⟨c, x⟩}` for some `c ∈ S_d`; if `h ≤ 1`, then `c ∈ S_d^+`.
Formalization Note: the symmetric `c` is unique, so "then `c ∈ S_d^+`" is stated about that `c`. -/
theorem lemma_6_2 {d : ℕ} (h : AffinePSD.Necessity.Cone d → ℝ) (hmeas : Measurable h) (hpos : ∀ x, 0 < h x)
    (hmul : ∀ x y : AffinePSD.Necessity.Cone d, h (coneAdd x y) = h x * h y) :
    ∃ c : AffinePSD.Necessity.Mat d, AffinePSD.Necessity.IsSym c ∧ (∀ x : AffinePSD.Necessity.Cone d, h x = Real.exp (- AffinePSD.Necessity.tr c x.1)) ∧
      ((∀ x, h x ≤ 1) → AffinePSD.Necessity.PSD c) := by sorry

end AffinePSD.InfDiv
