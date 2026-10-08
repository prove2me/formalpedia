-- Prove2me | Theorems.Thm_DouglasRachfordPPA_GenDR_representation_lemma
-- name    : DouglasRachfordPPA.GenDR.representation_lemma
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:22:53.458138+00:00
-- url     : https://prove2.me/theorems/46fd4449-7aad-41aa-94da-f047d4f9e71d
-- title:
--   Corollary 2.3 (Representation Lemma) — unique decomposition $z=x+cy$, $y\in Tx$
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $c>0$, and $T$ a monotone operator on $\mathcal H$.
--
--   1. Every $z\in\mathcal H$ can be written in at most one way as $z=x+cy$ with $y\in Tx$: if $z=x+cy=x'+cy'$ with $y\in Tx$, $y'\in Tx'$, then $x=x'$ and $y=y'$.
--   2. If $T$ is maximal monotone, every $z\in\mathcal H$ can be written in exactly one way as $z=x+cy$ with $y\in Tx$.
--
--   The lemma is used to describe each Douglas–Rachford step by the unique pairs $(x^k,b^k)\in B$ with $x^k+\lambda b^k=z^k$.
--
--   **Formalization Note** "Exactly one way" is unique existence of the pair $(x,y)\in\mathcal H\times\mathcal H$.
-- source:
--   Eckstein and Bertsekas, On the Douglas–Rachford Splitting Method and the Proximal Point Algorithm for Maximal Monotone Operators, MIT LIDS-P-1919 (October 1989), p. 8, Corollary 2.3

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators

open InnerProductSpace ThreeOpSplitting.Convergence

namespace DouglasRachfordPPA.GenDR

/-- Corollary 2.3 (Representation Lemma): for `c > 0` and monotone `T`, every `z` can be
written in at most one way as `x + c y` with `y ∈ T x`; if `T` is maximal, in exactly one way. -/
theorem representation_lemma {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (c : ℝ) (hc : 0 < c) (T : H → Set H) (hT : IsMonotoneOp T) :
    (∀ z x y x' y' : H, y ∈ T x → y' ∈ T x' → z = x + c • y → z = x' + c • y' →
      x = x' ∧ y = y') ∧
    (IsMaximalMonotone T → ∀ z : H, ∃! p : H × H, p.2 ∈ T p.1 ∧ z = p.1 + c • p.2) := by sorry

end DouglasRachfordPPA.GenDR
