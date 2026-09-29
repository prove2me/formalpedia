-- Prove2me | Theorems.Thm_CartierDual_exists_bialgEquiv_monoidAlgebra_of_points
-- name    : CartierDual.exists_bialgEquiv_monoidAlgebra_of_points
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/2ecfd84c-d5dc-5198-bfbd-6680f987059b
-- title:
--   Evaluation at convolution points identifies A with R[Γ]^∨
-- statement:
--   Let $R$ be a commutative ring, $A$ a commutative $R$-algebra equipped with an $R$-bialgebra structure, and $\Gamma$ a finite commutative monoid. Let $y$ be a homomorphism of monoids from $\Gamma$ to the set $A \to_{\mathrm{alg}[R]} R$ of $R$-algebra homomorphisms $A \to R$, the latter carried by `WithConv` with its convolution monoid structure (so $y(xx')$ is the convolution product $y(x) * y(x')$ and $y(1)$ is the unit of that monoid). Assume the evaluation map $A \to (\Gamma \to R)$, $a \mapsto (x \mapsto y(x)(a))$, is bijective. Then there exists an isomorphism of $R$-bialgebras $\psi$ from $A$ onto the Cartier dual of the monoid algebra $R[\Gamma]$ — by definition the $R$-module dual $\mathrm{Hom}_R(R[\Gamma], R)$, with the bialgebra structure dual to that of $R[\Gamma]$ — such that for all $a \in A$ and $x \in \Gamma$ the functional $\psi(a)$ takes the basis element `MonoidAlgebra.single x 1`, i.e. $[x]$, to $y(x)(a)$. Thus $\psi$ is evaluation at the points $y(x)$, and the assertion is that this map is not merely an $R$-algebra isomorphism but respects comultiplication as well.
--
--   This is the Cartier-duality recognition criterion for a bialgebra split by a convolution-closed family of $R$-points: a bialgebra whose points are exhausted by a finite commutative monoid $\Gamma$ is the coordinate ring of the diagonalisable scheme dual to the constant scheme $\Gamma$. It is used in the analysis of finite flat group schemes with prescribed cyclotomic inertia action, feeding the results [`GaloisRep.exists_bialgEquiv_monoidAlgebra_of_finiteFlatHopf_of_galoisCyclotomic`](thm.html#GaloisRep.exists_bialgEquiv_monoidAlgebra_of_finiteFlatHopf_of_galoisCyclotomic) and [`HopfAlgebra.exists_surjective_bialgHom_monoidAlgebra_of_inertiaCyclotomic_submonoid`](thm.html#HopfAlgebra.exists_surjective_bialgHom_monoidAlgebra_of_inertiaCyclotomic_submonoid).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CartierDual_exists_bialgEquiv_monoidAlgebra_of_points.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CartierDual.exists_bialgEquiv_monoidAlgebra_of_points
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Bialgebra R A]
    (Γ : Type*) [CommMonoid Γ] [Finite Γ]
    (y : Γ →* WithConv (A →ₐ[R] R))
    (hy : Function.Bijective fun (a : A) (x : Γ) => y x a) :
    ∃ ψ : A ≃ₐc[R] CartierDual R (MonoidAlgebra R Γ),
      ∀ (a : A) (x : Γ), ψ a (MonoidAlgebra.single x 1) = y x a := by sorry
