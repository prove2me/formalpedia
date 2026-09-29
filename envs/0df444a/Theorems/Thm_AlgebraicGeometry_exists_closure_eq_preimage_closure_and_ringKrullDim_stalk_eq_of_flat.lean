-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_closure_eq_preimage_closure_and_ringKrullDim_stalk_eq_of_flat
-- name    : AlgebraicGeometry.exists_closure_eq_preimage_closure_and_ringKrullDim_stalk_eq_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/371b041e-8bac-5b85-82e6-b975c26e9a16
-- title:
--   Generic point of G×_k w̄ and its local dimension
-- statement:
--   Let $k$ be a field and let $G$ and $P$ be schemes, with morphisms $f \colon G \to \operatorname{Spec} k$ and $p \colon P \to \operatorname{Spec} k$. Assume $f$ is geometrically irreducible and locally of finite type, and that $p$ is locally of finite type. Let $w$ be a point of $P$. Form the fibre product $G \times_k P$ (the pullback of $f$ along $p$) with its second projection $\operatorname{pr}_2 \colon G \times_k P \to P$. The assertion is that there exists a point $\zeta$ of $G \times_k P$ such that: the closure of $\{\zeta\}$ in $G \times_k P$ is exactly the preimage under the underlying continuous map of $\operatorname{pr}_2$ of the closure of $\{w\}$ in $P$ (so this closed subset, set-theoretically $G \times_k \overline{\{w\}}$, is irreducible with generic point $\zeta$); the image of $\zeta$ under $\operatorname{pr}_2$ is $w$; and the Krull dimension of the stalk of the structure sheaf of $G \times_k P$ at $\zeta$ equals the Krull dimension of the stalk of the structure sheaf of $P$ at $w$.
--
--   This is the scheme-theoretic form of the classical statement that for a variety $G$ and a subvariety $Z$ of codimension $r$ in $P$, the product $G \times Z$ is an irreducible subvariety of codimension $r$ in $G \times P$; it combines the stability of geometric irreducibility under base change with the additivity of dimension along a flat local homomorphism, the fibre contribution vanishing at a generic point of the fibre. In the present development it serves the construction, in the style of Rosenlicht, of divisors stable under a partial group action: it is used to produce a generic point of a prime divisor of $G \times_k P$ above a prime divisor of $P$ and thence to obtain stability statements for such divisors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_closure_eq_preimage_closure_and_ringKrullDim_stalk_eq_of_flat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_closure_eq_preimage_closure_and_ringKrullDim_stalk_eq_of_flat
    {k : Type u} [Field k] {G P : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    (p : P ⟶ Spec (CommRingCat.of k))
    [GeometricallyIrreducible f] [LocallyOfFiniteType f] [LocallyOfFiniteType p] (w : P) :
    ∃ ζ : ↥(pullback f p),
      closure ({ζ} : Set ↥(pullback f p)) = (pullback.snd f p).base ⁻¹' closure ({w} : Set P) ∧
      (pullback.snd f p).base ζ = w ∧
      ringKrullDim ((pullback f p).presheaf.stalk ζ) = ringKrullDim (P.presheaf.stalk w) := by sorry
