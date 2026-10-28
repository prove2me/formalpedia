-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_normal_projective_base_with_curve_family_of_finite_generic_parameter
-- name    : AlgebraicGeometry.exists_normal_projective_base_with_curve_family_of_finite_generic_parameter
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-26T17:21:23.633429+00:00
-- url     : https://prove2.me/theorems/020f1d4e-339b-4877-8d7e-39d5ef7d5a9d
-- title:
--   A global projective curve-family model from a supplied finite generic parameter
-- statement:
--   Let $k$ be a field and let $S$ be an integral proper projective $k$-scheme. Let $M$ be a proper projective $k$-scheme with a specified proper flat family $f:C\to M$ whose geometric fibres are reduced, connected and nonempty. A closed projective embedding of the total parameter family $C$ over $k$ is also specified.
--
--   Let $\eta$ be the actual generic point of $S$, let $E/\kappa(\eta)$ be a finite extension with its compatible $k$-algebra structure, and let $m:\operatorname{Spec}E\to M$ be a $k$-point over $E$. Suppose a specified cartesian source $C_0/E$ of $f$ at $m$ is smooth, geometrically integral and has dimension one.
--
--   There are a normal integral projective base $T$, a proper surjection $q:T\to S$, a proper parameter map $b:T\to M$, a dominant preimmersion $t:\operatorname{Spec}E\to T$, and an actual cartesian family
--   $$X=C\times_M T,\qquad p:X\longrightarrow T.$$
--   The total space $X$ is integral and projective over $k$. The morphism $p$ is proper, flat, surjective, geometrically reduced and geometrically connected, and $\dim T=\dim S$.
--
--   The prescribed $C_0$ is retained as the actual cartesian source of $p$ over the same field point $t$, with its map to $C$ recovered exactly. Both generic equations are retained: $q\circ t$ is the prescribed generic spectrum map to $S$ and $b\circ t=m$. The actual fibre of $p$ over every generic point of $T$ is a smooth proper geometrically integral curve of dimension exactly one. An explicit isomorphism from $C_0$ to this generic fibre, together with the corresponding field-spectrum isomorphism and both projection equations, is part of the conclusion.
--
--   Closed projective embeddings of the same $T$ and $X$ have structure maps exactly $q$ followed by the structure map of $S$, and $p$ followed by that composite, respectively. The theorem assumes the supplied projective parameter family and its classifying point. It does not construct a stable-curve parameter space, assert nodal fibres, extend a map to an additional target, or assert smoothness of the whole total space.
-- source:
--   Auxiliary parameter-family realization for A. J. de Jong, Smoothness, semi-stability and alterations, Publications Mathématiques de l’IHÉS 83 (1996), Section 4.17, pp. 71-72, https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf . This is the pullback-family step after a supplied finite generic parameter is extended to a normal projective base; it uses the accepted parameter-model theorem https://prove2.me/theorems/9afbffc7-8dee-40bf-9031-f73fed45feef and projective product embedding https://prove2.me/theorems/15fbefcf-89ea-5e7d-bf8e-af6412e75b66 . It is an auxiliary derived statement, not a verbatim numbered theorem. Total integrality follows from the dense integral generic fibre and reducedness of the flat geometrically reduced family. Stable moduli, nodal structure, extension to the original total-space target and boundary regularization remain additional obligations.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_normal_projective_base_with_curve_family_of_finite_generic_parameter
    (k : Type u) [Field k] {S M C C₀ : Scheme.{u}} [IsIntegral S]
    (πS : S ⟶ Spec (.of k)) [IsProper πS]
    (dS : ℕ) (iS : S ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dS + 1)) k))
    [IsClosedImmersion iS] (hiS : iS ≫ ProjSpace.π k dS = πS)
    (πM : M ⟶ Spec (.of k)) [IsProper πM]
    (dM : ℕ) (iM : M ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dM + 1)) k))
    [IsClosedImmersion iM] (hiM : iM ≫ ProjSpace.π k dM = πM)
    (f : C ⟶ M) [IsProper f] [Flat f] [GeometricallyReduced f] [GeometricallyConnected f]
    (dC : ℕ) (iC : C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dC + 1)) k))
    [IsClosedImmersion iC] (hiC : iC ≫ ProjSpace.π k dC = f ≫ πM)
    (η : S) (hη : IsGenericPoint η Set.univ) :
    letI : Algebra k (S.residueField η) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ πS.appTop ≫
        S.presheaf.germ ⊤ η trivial ≫ S.residue η).hom.toAlgebra
    ∀ (E : Type u) [Field E] [Algebra (S.residueField η) E] [Algebra k E]
      [IsScalarTower k (S.residueField η) E] [FiniteDimensional (S.residueField η) E]
      (m : Spec (.of E) ⟶ M)
      (hm : m ≫ πM = Spec.map (CommRingCat.ofHom (algebraMap k E)))
      (e₀ : C₀ ⟶ C) (p₀ : C₀ ⟶ Spec (.of E)) [Smooth p₀] [GeometricallyIntegral p₀]
      (h₀ : IsPullback e₀ p₀ f m) (hd₀ : topologicalKrullDim C₀ = 1),
    ∃ (T : Scheme.{u}) (q : T ⟶ S) (b : T ⟶ M) (t : Spec (.of E) ⟶ T)
      (X : Scheme.{u}) (p : X ⟶ T) (l : X ⟶ C) (e : C₀ ⟶ X),
      IsIntegral T ∧ (∀ x : T, IsIntegrallyClosed (T.presheaf.stalk x)) ∧
      IsProper q ∧ Surjective q ∧ IsProper b ∧ IsDominant t ∧ IsPreimmersion t ∧
      t ≫ q = Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) E)) ≫
        S.fromSpecResidueField η ∧ t ≫ b = m ∧ q ≫ πS = b ≫ πM ∧
      topologicalKrullDim T = topologicalKrullDim S ∧
      IsIntegral X ∧ IsProper p ∧ Flat p ∧ GeometricallyReduced p ∧
      GeometricallyConnected p ∧ Surjective p ∧ IsPullback l p f b ∧
      IsPullback e p₀ p t ∧ e ≫ l = e₀ ∧
      (∀ ηT : T, IsGenericPoint ηT Set.univ →
        Smooth (p.fiberToSpecResidueField ηT) ∧ IsProper (p.fiberToSpecResidueField ηT) ∧
        GeometricallyIntegral (p.fiberToSpecResidueField ηT) ∧ topologicalKrullDim (p.fiber ηT) = 1) ∧
      (∃ (dT : ℕ) (iT : T ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dT + 1)) k)),
        IsClosedImmersion iT ∧ iT ≫ ProjSpace.π k dT = q ≫ πS) ∧
      (∃ (dX : ℕ) (iX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dX + 1)) k)),
        IsClosedImmersion iX ∧ iX ≫ ProjSpace.π k dX = p ≫ q ≫ πS) ∧
      ∃ ηT : T, IsGenericPoint ηT Set.univ ∧
        ∃ γ : Spec (.of E) ⟶ Spec (T.residueField ηT),
          IsIso γ ∧ γ ≫ T.fromSpecResidueField ηT = t ∧
          ∃ a : C₀ ⟶ p.fiber ηT, IsIso a ∧
            a ≫ p.fiberι ηT = e ∧
            a ≫ p.fiberToSpecResidueField ηT = p₀ ≫ γ := by sorry
