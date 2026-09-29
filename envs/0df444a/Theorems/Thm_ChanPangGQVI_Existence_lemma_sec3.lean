-- Prove2me | Theorems.Thm_ChanPangGQVI_Existence_lemma_sec3
-- name    : ChanPangGQVI.Existence.lemma_sec3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:37:44.066645+00:00
-- url     : https://prove2.me/theorems/0007aaca-8683-4af7-9b57-5c4ca6e4e75a
-- title:
--   Lemma of §3 — a variational inequality on W ∩ E at an interior point extends to W
-- statement:
--   Let $W$ and $E$ be convex subsets of $\mathbb R^n$ with $E$ solid, that is, with nonempty interior $E^0$. Suppose that $x^0\in W\cap E^0$ and $y^*\in\mathbb R^n$ satisfy
--
--   $$
--   (x'-x^0)^T y^*\ \ge\ 0\qquad\text{for all } x'\in W\cap E .
--   $$
--
--   Then the same inequality holds for all $x'\in W$.
--
--   The lemma is the localisation step in the proof of Theorem 3.2: a solution of the variational inequality restricted to the compact set $C$ is a solution of the unrestricted problem as soon as the relevant point lies in the interior of $E$.
--
--   **Formalization Note** The set $E$ is called `Es` in Lean. The inequality glyph is illegible in the scan and is read as $\ge$ (a strict inequality would fail at $x'=x^0$).
-- source:
--   Chan and Pang, The generalized quasi-variational inequality problem, Math. Oper. Res. 7 (1982), p. 215, Section 3, Lemma (unnumbered, stated after Theorem 3.2)

import Mathlib

open scoped RealInnerProductSpace

namespace ChanPangGQVI.Existence

/-- Chan and Pang 1982, §3, Lemma (p. 215; unnumbered; proof in Fang and Peterson, reference [11]). Let `W`
and `E` be convex sets in `ℝⁿ` with `E` solid (nonempty interior). Suppose `x⁰ ∈ W ∩ E°` and
`y* ∈ ℝⁿ` satisfy `(x' - x⁰)ᵀ y* ≥ 0` for all `x' ∈ W ∩ E`. Then the same inequality holds for all
`x' ∈ W`. The inequality glyph is illegible in the scan and read as `≥` (`>` fails at `x' = x⁰`).
The set `E` is named `Es` in Lean. -/
theorem lemma_sec3 {n : ℕ} (W Es : Set (EuclideanSpace ℝ (Fin n)))
    (hW : Convex ℝ W) (hEs : Convex ℝ Es) (hEs_solid : (interior Es).Nonempty)
    (x0 ystar : EuclideanSpace ℝ (Fin n)) (hx0 : x0 ∈ W ∩ interior Es)
    (h : ∀ x' ∈ W ∩ Es, 0 ≤ ⟪x' - x0, ystar⟫) :
    ∀ x' ∈ W, 0 ≤ ⟪x' - x0, ystar⟫ := by sorry

end ChanPangGQVI.Existence
