-- Prove2me | Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_point_forall_mem_iff_of_isClosedImmersion_of_forall_geomFibreH0Finrank_eq_eval
-- name    : AlgebraicGeometry.HilbertFunctor.exists_point_forall_mem_iff_of_isClosedImmersion_of_forall_geomFibreH0Finrank_eq_eval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/5ca16e02-86be-5068-8c40-c08efcbb3553
-- title:
--   Hilbert-functor point from a closed subscheme with h⁰ = P
-- statement:
--   Let $n$ be a natural number and $P \in \mathbb{Q}[T]$, and assume `hP`: for some field $K$ there is an ideal $I \subseteq K[x_0,\dots,x_n]$ closed under taking homogeneous components (every homogeneous component of every element of $I$ lies in $I$) and a bound $d_1$ such that for all $d \ge d_1$ the $K$-dimension of `piece I d`, the space of degree-$d$ homogeneous polynomials modulo those lying in $I$, equals $P(d)$. The conclusion asserts a bound $D_0$ with the following property for every $m \ge D_0$: for every algebraically closed field $k$, every scheme $Z$ and every closed immersion $\iota : Z \to \operatorname{Proj} k[x_0,\dots,x_n]$, every sheaf of modules $\mathcal{L}$ on $Z$ that is invertible in the sense that every point has a neighbourhood $U$ on which the restriction of $\mathcal{L}$ is isomorphic to the unit sheaf, and every `ProjPresentation` $\mathfrak{P}$ of $\mathcal{L}$ over $\iota$ followed by the structure map $\operatorname{Proj} \to \operatorname{Spec} k$ with $n+1$ generating global sections $\sigma_i$ framing $\mathcal{L}$ over the preimages of the $D_+(x_i)$ and with prescribed ratio relations, whose associated morphism $\mathfrak{P}.\mathrm{toProj}$ is $\iota$ itself: if there is $d_0$ such that for all $d \ge d_0$ the geometric-fibre $h^0$-dimension over $k$ (along the identity of $k$) of the $d$-fold tensor power $\mathcal{L}^{\otimes d}$, formed by recursion with $\mathcal{L}^{\otimes 0}$ the unit, equals $P(d)$, then there exists a point $q$ of the Hilbert functor at $k$, i.e. a homogeneous-component-closed ideal $q.I \subseteq k[x_0,\dots,x_n]$ all of whose pieces are finite projective $k$-modules of rank at every prime equal to $\mathrm{hilbertFunctionOf}\,n\,P\,m\,(d) = \binom{n+d}{n}$ for $d < m$ and $\lfloor P(d) \rfloor$ (truncated to $\mathbb{N}$) for $d \ge m$, such that for every $d \ge m$ and every homogeneous $F$ of degree $d$ one has $F \in q.I$ if and only if for each $i$ the section $F/x_i^{d}$ on $D_+(x_i)$ pulls back to $0$ along $\iota$.
--
--   This is the converse direction of the dictionary between closed subschemes of $\mathbb{P}^n_k$ and points of the Hilbert functor: a closed subscheme whose invertible sheaf $\mathcal{L}$ (presented by the coordinate sections) has $h^0(\mathcal{L}^{\otimes d}) = P(d)$ for all large $d$ is cut out, in degrees $\ge m$, by a Hilbert-functor point with Hilbert function $\mathrm{hilbertFunctionOf}\,n\,P\,m$. It is used in the construction attached to framed polarised abelian schemes, where a point of the Hilbert functor must be produced from geometric data on a fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_HilbertFunctor_exists_point_forall_mem_iff_of_isClosedImmersion_of_forall_geomFibreH0Finrank_eq_eval.lean

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.HilbertFunctor.exists_point_forall_mem_iff_of_isClosedImmersion_of_forall_geomFibreH0Finrank_eq_eval
    (n : ℕ) (P : Polynomial ℚ)
    (hP : ∃ (K : Type) (_ : Field K) (I : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) ∧
      ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d → (Module.finrank K (piece I d) : ℚ) = P.eval (d : ℚ)) :
    ∃ D₀ : ℕ, ∀ m : ℕ, D₀ ≤ m → ∀ (k : Type) [Field k] [IsAlgClosed k]
      (Z : Scheme.{0}) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)), IsClosedImmersion ι →
      ∀ (𝓛 : Z.Modules) (_h𝓛 : Scheme.Modules.IsInvertible 𝓛)
        (𝔓 : Scheme.Modules.ProjPresentation 𝓛 (ι ≫ ProjSpace.π k n) n) (_h𝔓 : 𝔓.toProj = ι),
      (∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
        ((Scheme.Modules.geomFibreH0Finrank (ι ≫ ProjSpace.π k n)
          (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules) (fun _ M => M ⊗ 𝓛) d) k (RingHom.id k) : ℕ) : ℚ) =
          P.eval (d : ℚ)) →
      ∃ q : Point k n (hilbertFunctionOf n P m),
        ∀ (d : ℕ), m ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
          (F ∈ q.I ↔ ∀ i : Fin (n + 1),
            ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (X i))
              ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (X i))
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ })) = 0) := by sorry
