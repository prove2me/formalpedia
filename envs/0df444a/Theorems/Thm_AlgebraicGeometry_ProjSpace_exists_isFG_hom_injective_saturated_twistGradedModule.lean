-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule
-- name    : AlgebraicGeometry.ProjSpace.exists_isFG_hom_injective_saturated_twistGradedModule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/bf17b346-62f8-56da-b8fb-f3c8520cdd79
-- title:
--   Finitely generated saturated graded submodule of the twist module
-- statement:
--   Let $A$ be a commutative ring, $N$ a natural number and $X$ a scheme, and let $\varphi \colon X \to \operatorname{Proj} A[x_0,\dots,x_N]$ be a finite morphism to projective $N$-space over $A$ (formed from the standard grading of `MvPolynomial (Fin (N+1)) A` by its homogeneous submodules); let $\pi \colon X \to \operatorname{Spec} A$ be a morphism which factors as $\varphi$ followed by the structure morphism `ProjSpace.π A N` of $\mathbb{P}^N_A$. Write $M(\varphi) =$ `ProjSpace.twistGradedModule φ π` for the graded module attached to this datum: its underlying $A$-module consists of the families $f$ assigning to each $d \in \mathbb{Z}$ a tuple of sections $f\,d\,i \in \Gamma(X, \top \sqcap \varphi^{-1}D_+(x_i))$ over the pullback charts, the submodule of degree $d$ consists of those $f$ that vanish in all degrees $d' \neq d$, vanish altogether when $d < 0$, and whose degree-$d$ tuple satisfies the chart-compatibility condition `TwistCompat φ d.toNat ⊤`, and the operator `xMul j` sends $f$ to $d \mapsto (\,i \mapsto \mathrm{frameUnit}\,\varphi\,i\,j \cdot f(d-1)\,i\,)$, these $N+1$ commuting $A$-linear maps each raising degree by one. The assertion is that there exist another such graded module $M'$ over $(A,N)$ and a morphism $\psi \colon M' \to M(\varphi)$ of graded modules, i.e. an $A$-linear map carrying each graded piece of $M'$ into the corresponding piece of $M(\varphi)$ and commuting with all the operators `xMul j`, such that: (i) $M'$ is finitely generated, in the sense that it admits a presentation consisting of a finite index type $J$, degrees $d_0 \colon J \to \mathbb{Z}$ and a morphism from the product of the free graded modules `GradedModule.FD A N (d₀ k)` onto $M'$ which is surjective in every degree; (ii) $\psi$ is injective on underlying modules; and (iii) $\psi$ is saturated at each variable: for every $j \in \{0,\dots,N\}$, every $e \in \mathbb{Z}$ and every $x$ in the degree-$e$ piece of $M(\varphi)$, there are $k \in \mathbb{N}$ and an element $x'$ of the degree-$(e+k)$ piece of $M'$ with $\psi(x') = (\mathrm{xMul}\,j)^k x$.
--
--   This is the graded-module form of the statement that the twisted sections of a finite morphism to $\mathbb{P}^N_A$ agree, after inverting any one coordinate, with a finitely generated graded module, so that $M'$ and $M(\varphi)$ define the same quasi-coherent sheaf on $\mathbb{P}^N_A$. It supplies the finiteness input used in the Čech computations for the twist datum, and is cited by [`AlgebraicGeometry.ProjSpace.exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion`](thm.html#AlgebraicGeometry.ProjSpace.exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion) and [`AlgebraicGeometry.ProjSpace.exists_forall_subsingleton_HSucc_twist`](thm.html#AlgebraicGeometry.ProjSpace.exists_forall_subsingleton_HSucc_twist).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_isFG_hom_injective_saturated_twistGradedModule
    {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) [IsFinite φ]
    (π : X ⟶ Spec (.of A)) (hπ : φ ≫ ProjSpace.π A N = π) :
    ∃ (M' : ProjSpaceCech.GradedModule A N) (ψ : ProjSpaceCech.GradedModule.Hom M' (ProjSpace.twistGradedModule φ π)),
      M'.IsFG ∧ Function.Injective ψ.toLinearMap ∧
      ∀ (j : Fin (N + 1)) (e : ℤ), ∀ x ∈ (ProjSpace.twistGradedModule φ π).grade e,
        ∃ k : ℕ, ∃ x' ∈ M'.grade (e + k), ψ.toLinearMap x' = ((ProjSpace.twistGradedModule φ π).xMul j ^ k) x := by sorry
