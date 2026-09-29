-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_split
-- name    : AlgebraicGeometry.RelEffCartierDiv.exists_split
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/b7aed620-dcfb-535c-91b9-7df2f797594b
-- title:
--   Universal splitting cover of degree r! for a relative divisor
-- statement:
--   Let $f \colon \mathcal{C} \to S$ be a morphism of schemes which is separated and smooth of relative dimension $1$, let $r$ be a natural number, let $g \colon T \to S$ be an $S$-scheme, and let $D$ be a relative effective Cartier divisor of degree $r$ for $f$ over $g$, that is, an ideal sheaf datum $D.I$ on $\mathcal{C} \times_S T$ whose closed subscheme inclusion followed by the projection to $T$ is finite, flat and locally of finite presentation with fibre rank $r$ at every point of $T$. The assertion is that there exist a scheme $P$, a structure morphism $gP \colon P \to S$, a morphism $p \colon P \to T$ with $p$ followed by $g$ equal to $gP$, and $r$ morphisms $b_i \colon P \to \mathcal{C}$ over $S$ (each $b_i$ followed by $f$ equal to $gP$), such that: $p$ is finite, flat, locally of finite presentation and surjective; $p$ has fibre rank $r!$ at every point of $T$; the ideal of the pullback of $D$ along $p$, namely $D.I$ pulled back by the induced map $\mathcal{C} \times_S P \to \mathcal{C} \times_S T$, equals the product $\prod_i \ker(\operatorname{graph} b_i)$ of the kernel ideals of the graph sections $P \to \mathcal{C} \times_S P$ of the $b_i$; and this datum is universal: for every $S$-scheme $g' \colon T' \to S$, every $q \colon T' \to T$ with $q$ followed by $g$ equal to $g'$, and every family $b'_i \colon T' \to \mathcal{C}$ of $S$-morphisms satisfying the same product-of-graph-kernels identity for the pullback of $D$ along $q$, there is a unique $u \colon T' \to P$ with $u$ followed by $p$ equal to $q$ and $u$ followed by $b_i$ equal to $b'_i$ for all $i$.
--
--   This is the representability of the functor of ordered splittings of a relative effective divisor of degree $r$ into a sum of $r$ sections: the splitting functor is represented by a finite, flat, surjective $T$-scheme of rank $r!$ carrying a tautological splitting. Nothing stronger is claimed — $p$ is not asserted étale or a principal $\mathfrak{S}_r$-bundle. It is used in the construction of universal divisors and symmetric-power-type parameter spaces, for instance in the results on sum maps for universal divisors, on divisors over algebraically closed fields being products of graph kernels, and on the existence of universal divisors over affine bases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_exists_split.lean

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.exists_split
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {r : ℕ} {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f r g) :
    ∃ (P : Scheme.{u}) (gP : P ⟶ S) (p : P ⟶ T) (hp : p ≫ g = gP)
      (b : Fin r → (P ⟶ 𝒞)) (hb : ∀ i, b i ≫ f = gP),
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      (∀ t : T, p.finrank t = r.factorial) ∧
      (D.pullbackAlong p hp).I = prodKerGraph f b hb ∧
      ∀ ⦃T' : Scheme.{u}⦄ (g' : T' ⟶ S) (q : T' ⟶ T) (hq : q ≫ g = g')
        (b' : Fin r → (T' ⟶ 𝒞)) (hb' : ∀ i, b' i ≫ f = g'),
        (D.pullbackAlong q hq).I = prodKerGraph f b' hb' →
        ∃! u : T' ⟶ P, u ≫ p = q ∧ ∀ i, u ≫ b i = b' i := by sorry
