-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_forall_isPullback_toProj_of_forall_away
-- name    : AlgebraicGeometry.Scheme.Modules.exists_projPresentation_forall_isPullback_toProj_of_forall_away
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/eb39d47b-3382-549e-91ed-ecc77acaa4ee
-- title:
--   Projective presentations glued along a principal cover of the base
-- statement:
--   Let $S$ be a commutative ring, let $r_1,\dots,r_k \in S$ (indexed by `Fin k`) generate the unit ideal, and for each $i$ let $B_i$ be an $S$-algebra realising the localisation of $S$ away from $r_i$. Let $f : A \to \operatorname{Spec} S$ be a morphism of schemes, and for each $i$ let $f' _i : A'_i \to \operatorname{Spec} B_i$ and $g_i : A'_i \to A$ form a cartesian square over $\operatorname{Spec} B_i \to \operatorname{Spec} S$. Assume $f$ is proper, and let $M$ be a module over $A$ which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ on which the pullback of $M$ along the inclusion of $U$ is isomorphic to the unit sheaf of modules. Let $M'_i$ be modules over $A'_i$ together with isomorphisms $g_i^{*}M \cong M'_i$, and suppose each $M'_i$ carries a projective presentation $\mathfrak Q_i$ relative to $f'_i$ of size $N'_i$, that is: sections $\sigma_0,\dots,\sigma_{N'_i}$ of $M'_i$ over the whole space, a morphism to $\operatorname{Proj}$ of the homogeneous subalgebra of $B_i[X_0,\dots,X_{N'_i}]$ composing with the structure projection to $f'_i$, such that on every open contained in the preimage of the basic open $D(X_j)$ multiplication by the restriction of $\sigma_j$ is a bijection from functions to sections, and such that the pullback of the ratio $X_j/X_l$ carries $\sigma_l$ to $\sigma_j$ over $D(X_l)$. Then there are an $N$ and a projective presentation $\mathfrak P$ of $M$ relative to $f$ of size $N$ such that for every $i$ there is a projective presentation $\mathfrak P'_i$ of $M'_i$ relative to $f'_i$, of the same size $N$, whose structure morphism makes the square with $g_i$, $\mathfrak P.\mathrm{toProj}$ and $\mathbb P^N_{B_i} \to \mathbb P^N_S$ cartesian, and such that each section $(\mathfrak Q_i).\sigma_j$ is a $B_i$-linear combination $\sum_l a_l \cdot (\mathfrak P'_i).\sigma_l$ of the sections of $\mathfrak P'_i$, the coefficients $a_l \in B_i$ acting through the identification of $B_i$ with the global functions on $\operatorname{Spec} B_i$ followed by $(f'_i)^{*}$.
--
--   This is the statement that a presentation of an invertible module by global sections, hence a morphism to projective space over the base, can be produced globally from presentations over the members of a principal affine cover of the base, with the local presentations expressed in the resulting global one; classically this is the fact that very ampleness and the associated morphism to $\mathbb P^N$ are local on the base (EGA II §4.4). It is used to establish [`AlgebraicGeometry.Scheme.Modules.closedImmersionBySections_of_forall_isPullback_away`](thm.html#AlgebraicGeometry.Scheme.Modules.closedImmersionBySections_of_forall_isPullback_away), the corresponding descent of the property that the sections of an invertible module define a closed immersion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_forall_isPullback_toProj_of_forall_away.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.exists_projPresentation_forall_isPullback_toProj_of_forall_away
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    {A' : Fin k → Scheme.{u}} (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (B i))) (g : ∀ i, A' i ⟶ A)
    (hg : ∀ i, IsPullback (g i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))))
    (hf : IsProper f) (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    (M' : ∀ i, (A' i).Modules) (e : ∀ i, (Scheme.Modules.pullback (g i)).obj M ≅ M' i)
    (N' : Fin k → ℕ) (𝔔 : ∀ i, Scheme.Modules.ProjPresentation (M' i) (f' i) (N' i)) :
    ∃ (N : ℕ) (𝔓 : Scheme.Modules.ProjPresentation M f N),
      ∀ i, ∃ 𝔓' : Scheme.Modules.ProjPresentation (M' i) (f' i) N,
        IsPullback (g i) 𝔓'.toProj 𝔓.toProj (ProjSpace.map S (B i) N) ∧
        ∀ j : Fin (N' i + 1), ∃ a : Fin (N + 1) → B i,
          (𝔔 i).σ j = ∑ l, (((f' i).appLE ⊤ ⊤ le_top).hom
            ((Scheme.ΓSpecIso (CommRingCat.of (B i))).inv.hom (a l))) • 𝔓'.σ l := by sorry
