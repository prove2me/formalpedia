-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/040eceda-1925-55bf-adcc-b73e83e4440a
-- title:
--   Base change of a projective presentation along a cartesian square
-- statement:
--   Let $R \to A$ be a homomorphism of commutative rings, let $X, X'$ be schemes, and let $f : X \to \operatorname{Spec} R$, $f' : X' \to \operatorname{Spec} A$ and $p : X' \to X$ be morphisms forming a cartesian square with $\operatorname{Spec}$ of the structure map $R \to A$, i.e. $p$ followed by $f$ equals $f'$ followed by $\operatorname{Spec}(R \to A)$ and the square is a pullback. Let $M$ be a module on $X$ (an object of `X.Modules`), let $N$ be a natural number, and let $\mathfrak{P}$ be a `ProjPresentation` of $M$ over $f$ of size $N$: that is, global sections $\sigma_0, \dots, \sigma_N$ of $M$, a morphism $\varphi = \mathfrak{P}.\mathrm{toProj}$ from $X$ to $\operatorname{Proj}$ of the graded ring of homogeneous polynomials in $N+1$ variables over $R$ whose composition with the structural projection $\mathbb{P}^N_R \to \operatorname{Spec} R$ is $f$, such that for every $i$ and every open $V \subseteq \varphi^{-1}(D_+(X_i))$ the map $g \mapsto g \cdot \sigma_i|_V$ from $\Gamma(X, V)$ to $\Gamma(M, V)$ is bijective, and such that on $\varphi^{-1}(D_+(X_i))$ the pullback along $\varphi$ of the degree-zero ratio $X_j/X_i$ multiplies $\sigma_i$ into $\sigma_j$. The conclusion asserts the existence of a `ProjPresentation` $\mathfrak{P}'$ of the pullback module $p^* M$ over $f'$ of the same size $N$ whose sections are the images $\sigma_i \mapsto \mathfrak{P}'.\sigma_i$ under the unit of the adjunction between pullback and pushforward of modules along $p$ evaluated at the top open, such that $\mathfrak{P}'.\mathrm{toProj}$ followed by `ProjSpace.map R A N` $: \mathbb{P}^N_A \to \mathbb{P}^N_R$ equals $p$ followed by $\varphi$, and such that the resulting square with sides $p$, $\mathfrak{P}'.\mathrm{toProj}$, $\varphi$ and `ProjSpace.map R A N` is cartesian.
--
--   This is the base-change statement for a morphism to projective space presented by generating sections of a module: a presentation over $R$ induces one over $A$ after pullback, with the induced map to $\mathbb{P}^N_A$ cartesian over the map to $\mathbb{P}^N_R$. Stating the conclusion as a cartesian square rather than via a chosen fibre product lets it be applied to base change to a field, to a localisation, and iteratively; it is used in the construction of frames and theta-adapted data on polarised abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {X X' : Scheme.{u}}
    {f : X ⟶ Spec (.of R)} {f' : X' ⟶ Spec (.of A)} {p : X' ⟶ X}
    (sq : IsPullback p f' f (Spec.map (CommRingCat.ofHom (algebraMap R A))))
    {M : X.Modules} {N : ℕ} (𝔓 : M.ProjPresentation f N) :
    ∃ 𝔓' : ((Scheme.Modules.pullback p).obj M).ProjPresentation f' N,
      (∀ i, 𝔓'.σ i = (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤) (𝔓.σ i)) ∧
      𝔓'.toProj ≫ ProjSpace.map R A N = p ≫ 𝔓.toProj ∧
      IsPullback p 𝔓'.toProj 𝔓.toProj (ProjSpace.map R A N) := by sorry
