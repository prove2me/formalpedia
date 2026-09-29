-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre_of_hom
-- name    : AlgebraicGeometry.exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre_of_hom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/edb24311-5d58-5e01-9997-b13cd4c1c742
-- title:
--   Geometric fibre Hilbert function read off a defining ideal
-- statement:
--   Let $S$ be a commutative ring, $f : X \to \operatorname{Spec} S$ a morphism of schemes, and $\mathcal{L}_X$ an $\mathcal{O}_X$-module that is invertible in the sense that every point of $X$ has an open neighbourhood $U$ on which the restriction of $\mathcal{L}_X$ is isomorphic to the unit module. Let $\mathfrak{P}$ be a `ProjPresentation` of $\mathcal{L}_X$ over $f$ in degree $n$: sections $\sigma_0,\dots,\sigma_n$ of $\mathcal{L}_X$ over $X$, a morphism $\mathfrak{P}.\mathrm{toProj} : X \to \mathbf{P}^n_S = \operatorname{Proj}$ of the graded algebra of homogeneous components of $S[x_0,\dots,x_n]$ lying over $f$, such that on each open set contained in the preimage of $D_+(x_i)$ multiplication by $\sigma_i$ is bijective, and such that the ratios $x_j/x_i$ act on $\sigma_i$ to give $\sigma_j$. Let $S'$ be a commutative ring, $s : \operatorname{Spec} S' \to \operatorname{Spec} S$ a morphism, and $\psi : S \to S'$ a ring homomorphism with $s = \operatorname{Spec}(\psi)$. Let $\iota : Z \to X_{S'} := X \times_{\operatorname{Spec} S, s} \operatorname{Spec} S'$ be a morphism, and $j : X_{S'} \to \mathbf{P}^n_{S'}$ a morphism over $S'$ (i.e. $j$ followed by the structure morphism is the second projection) whose composite with the base-change morphism $\mathbf{P}^n_{S'} \to \mathbf{P}^n_S$ attached to $\psi$ equals the first projection followed by $\mathfrak{P}.\mathrm{toProj}$. Let $k$ be an algebraically closed field and $sk : S' \to k$ a ring homomorphism. Let $P' \in \mathbb{Q}[T]$, $m' \in \mathbb{N}$, and write $h = \mathrm{hilbertFunctionOf}\,n\,P'\,m'$, so $h(d) = \binom{n+d}{n}$ for $d < m'$ and $h(d) = \lfloor P'(d)\rfloor$ (truncated to $\mathbb{N}$) otherwise. Let $q$ be a point of the Hilbert functor over $k$ with Hilbert function $h$: a homogeneous ideal $q.I \subseteq k[x_0,\dots,x_n]$ (stable under taking homogeneous components) all of whose graded quotient pieces are finite and projective $k$-modules of rank $h(d)$ at every prime. Finally let $\iota_k : Z_k \to \mathbf{P}^n_k$ be a closed immersion and $e : Z_k \to Z$ a morphism such that the square formed by $e$, $\iota_k$ followed by the structure morphism of $\mathbf{P}^n_k$, $\iota$ followed by the second projection, and $\operatorname{Spec}(sk)$ is cartesian, such that $\iota_k$ followed by the base-change morphism $\mathbf{P}^n_k \to \mathbf{P}^n_{S'}$ equals $e$ followed by $\iota$ followed by $j$, and such that for every $d \ge m'$ and every homogeneous $F$ of degree $d$ one has $F \in q.I$ if and only if for every $i$ the section $F/x_i^{d}$ of $\mathbf{P}^n_k$ over $D_+(x_i)$ restricts to $0$ along $\iota_k$. Then there is $d_0$ such that for all $d \ge d_0$ the $k$-dimension of the global sections of the $d$-th tensor power of the pullback of $\mathcal{L}_X$ to $Z$ (formed by recursion from the unit module, tensoring at each step with the pullback of $\mathcal{L}_X$ along $\iota$ followed by the first projection) over the geometric fibre of $\iota$ followed by the second projection at $sk$ equals $h(d)$.
--
--   This is the statement that, for a family $Z \subseteq X_{S'}$ presented projectively by an invertible module $\mathcal{L}_X$, the Hilbert function of the geometric fibre $Z_{\bar s}$ in large degrees is computed by the prescribed function $\mathrm{hilbertFunctionOf}\,n\,P'\,m'$, as soon as the fibre is cut out in $\mathbf{P}^n_k$ by the ideal of a point of the Hilbert functor with that Hilbert function. It is the form of the result used where the test morphism $s$ is an arbitrary morphism of affine schemes known only to come from a ring homomorphism, and it is cited in the construction of the representing scheme for the flat, finitely presented closed subschemes with given Hilbert polynomial, and in the corresponding covering statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre_of_hom.lean

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor NeronModelInfra GoodReductionJacobian
open MonoidalCategory
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre_of_hom
    (S : Type) [CommRing S] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of S))
    (𝓛X : X.Modules) (hX₁ : Scheme.Modules.IsInvertible 𝓛X)
    {n : ℕ} (𝔓 : Scheme.Modules.ProjPresentation 𝓛X f n)
    (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (ψ : S →+* S') (hs : s = Spec.map (CommRingCat.ofHom ψ))
    (Z : Scheme.{0}) (ι : Z ⟶ pullback f s)
    (j : pullback f s ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S'))
    (hj₁ : j ≫ ProjSpace.π S' n = pullback.snd f s)
    (hj₂ : (letI : Algebra S S' := ψ.toAlgebra; j ≫ ProjSpace.map S S' n) = pullback.fst f s ≫ 𝔓.toProj)
    (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k)
    (P' : Polynomial ℚ) (m' : ℕ) (q : Point k n (hilbertFunctionOf n P' m'))
    (Zk : Scheme.{0}) (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) (hιk : IsClosedImmersion ιk)
    (e : Zk ⟶ Z)
    (he₁ : IsPullback e (ιk ≫ ProjSpace.π k n) (ι ≫ pullback.snd f s) (Spec.map (CommRingCat.ofHom sk)))
    (he₂ : (letI : Algebra S' k := sk.toAlgebra; ιk ≫ ProjSpace.map S' k n) = e ≫ ι ≫ j)
    (hZk : ∀ d : ℕ, m' ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
      (F ∈ q.I ↔ ∀ i : Fin (n + 1),
        (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
          ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))
            (HomogeneousLocalization.mk
              { deg := d
                num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                den_mem := ⟨d, rfl⟩ })) = 0)) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
        (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
          (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk =
      hilbertFunctionOf n P' m' d := by sorry
