-- Prove2me | Theorems.Thm_AlgebraicGeometry_DescentCharacter_hasValue_symm_of_mul_eq_one
-- name    : AlgebraicGeometry.DescentCharacter.hasValue_symm_of_mul_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/76fd0a89-f764-5d53-8c71-96cd46558a44
-- title:
--   Inverse identification carries the inverse descent value
-- statement:
--   Let $X$ and $Y$ be schemes, $R$ a commutative ring, and $f \colon X \to \operatorname{Spec}(R)$ a morphism of schemes. Let $T \colon X \to X$ and $q \colon X \to Y$ be morphisms with $q \circ T = q$ (written $T \gg q = q$ in diagrammatic order), and let $N$, $M$ be objects of `Y.Modules`. Let $\beta$ be an isomorphism from $q^{*}N$ to $q^{*}M$, where $q^{*}$ denotes `Scheme.Modules.pullback q`, and let $c, c' \in R$. Assume `HasValue f h β c`, that is: the forward component of `discrepancy h β`, the composite of $\beta^{-1}$ followed by the $T$-translate `translateIso h β` of $\beta$, is multiplication by the base section of $c$, in the sense that for every open $U \subseteq X$ and every section $s$ of $q^{*}M$ over $U$ its component at $U$ sends $s$ to `baseSection f c U • s`. Assume further that $c' c = 1$ in $R$. Then `HasValue f h β.symm c'` holds: the forward component of the discrepancy of the inverse isomorphism $\beta^{-1} \colon q^{*}M \cong q^{*}N$ is, on sections over every open set, multiplication by the base section of $c'$.
--
--   This records that the descent character attached to an identification of pullbacks along $q$ of $\mathcal{O}_Y$-modules, measured at an endomorphism $T$ over $q$, is inverted when the identification is inverted; in the guiding case of an abelian scheme with $q = [n]$ and $T$ a translation by an $n$-torsion point, it corresponds to the relation $e_n(a, N^{-1}) = e_n(a, N)^{-1}$ for the Weil pairing. It is used in the construction of torsion characters attached to polarisations, in the two results on two-torsion descent characters that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_DescentCharacter_hasValue_symm_of_mul_eq_one.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.DescentCharacter

universe u

theorem AlgebraicGeometry.DescentCharacter.hasValue_symm_of_mul_eq_one
    {X Y : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {N M : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (c c' : R) (hβ : HasValue f h β c) (hc : c' * c = 1) :
    HasValue f h β.symm c' := by sorry
