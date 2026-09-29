-- Prove2me | Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point
-- name    : AlgebraicGeometry.HilbertFunctor.exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/0c968813-71e6-5443-9b54-c0be6665f6e5
-- title:
--   Large-degree h⁰ of tensor powers equals the Hilbert function
-- statement:
--   Fix $n, m \in \mathbb{N}$, a polynomial $P$ over $\mathbb{Q}$, and an algebraically closed field $k$. Write $h =$ `hilbertFunctionOf n P m`, so $h(d) = \binom{n+d}{n}$ for $d < m$ and $h(d) = \max(\lfloor P(d)\rfloor, 0)$ for $d \ge m$. Let $q$ be a point of the Hilbert functor for $h$: an ideal $q.I \subseteq k[x_0,\dots,x_n]$ closed under passage to homogeneous components, such that each quotient of the degree-$d$ forms by those lying in $q.I$ is a finite projective $k$-module whose rank at every prime of $k$ is $h(d)$. Let $\iota : Z \to \operatorname{Proj} k[x_0,\dots,x_n]$ be a closed immersion of schemes, and assume that for every $d \ge m$ and every homogeneous $F$ of degree $d$ one has $F \in q.I$ exactly when, for each $i$, the pullback along $\iota$ of the degree-zero section $F/x_i^d$ over the basic open set $D(x_i)$ vanishes on $\iota^{-1}D(x_i)$. Let $\mathcal{L}$ be an invertible module on $Z$ (locally isomorphic to the structure sheaf), equipped with a `ProjPresentation` relative to $\iota$ followed by the projection $\operatorname{Proj} \to \operatorname{Spec} k$, with $n+1$ global sections $\sigma_i$ framing $\mathcal{L}$ over the charts $\iota^{-1}D(x_i)$ and satisfying the coordinate-ratio relations, whose associated map to $\operatorname{Proj}$ is $\iota$ itself. Then there is $d_0$ such that for all $d \ge d_0$ the $k$-dimension of the global sections of the $d$-fold tensor power $\mathcal{L}^{\otimes d}$ (formed by iterated tensoring from the unit module), computed as the geometric-fibre $h^0$ along the identity ring map of $k$, equals $h(d)$.
--
--   This is the comparison, for large degrees, between the graded data carried by an ideal point of the Hilbert functor and the dimension of global sections of the powers of the tautological invertible module on the closed subscheme it cuts out — the step that converts Hilbert-function bookkeeping into $h^0$ bookkeeping. It is used in the construction of Hilbert-type parameter schemes, in particular by the recovery of an ideal point from $h^0$ data and by the emptiness criterion for framed polarised abelian schemes without a Hilbert polynomial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_HilbertFunctor_exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point.lean

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.HilbertFunctor.exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point
    (n : ℕ) (P : Polynomial ℚ) (m : ℕ) (k : Type) [Field k] [IsAlgClosed k]
    (q : Point k n (hilbertFunctionOf n P m))
    (Z : Scheme.{0}) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
    (hι : IsClosedImmersion ι)

    (hZ : ∀ d : ℕ, m ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
      (F ∈ q.I ↔ ∀ i : Fin (n + 1),
        (ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
          (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
            (HomogeneousLocalization.mk
              { deg := d
                num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                  (MvPolynomial.isHomogeneous_X_pow i d)⟩
                den_mem := ⟨d, rfl⟩ })) = 0))

    (𝓛 : Z.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (𝔓 : Scheme.Modules.ProjPresentation 𝓛 (ι ≫ ProjSpace.π k n) n) (h𝔓 : 𝔓.toProj = ι) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      Scheme.Modules.geomFibreH0Finrank (ι ≫ ProjSpace.π k n)
          (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules) (fun _ M => M ⊗ 𝓛) d) k (RingHom.id k) =
        hilbertFunctionOf n P m d := by sorry
