-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_isPullback_refl_comp_cancel_iso_symm_trans
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.isPullback_refl_comp_cancel_iso_symm_trans
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/7bbd468b-fd70-54fc-88b9-90ae3de99608
-- title:
--   Base-change and isomorphism calculus for polarised abelian schemes
-- statement:
--   Fix natural numbers $g$, $d$, $n$. For a commutative ring $S$, an element $u$ of `PolarisedAbelianScheme g d n S` consists of a scheme $u.A$ with a structure morphism $u.f \colon u.A \to \operatorname{Spec} S$, a relative group law $u.L$ on the functor of points $T \mapsto \{\,x \colon T \to u.A \mid x \text{ over } t\,\}$ which is commutative, the property bundle (smooth, proper, connected fibres, a group law exists), all fibres of topological Krull dimension $g$, sections $u.P_i$ ($i < 2g$) of $u.f$ that are $n$-torsion and form a basis of the $n$-torsion on every geometric fibre, together with a module $u.\mathrm{pol}$ on $u.A$ that is invertible, defines a closed immersion by sections over $u.f$, and has geometric fibre $H^0$-rank $d$. For a ring map $\varphi \colon S \to S'$, `IsPullback φ u u'` asserts the existence of $g_A \colon u'.A \to u.A$ making the square with $u'.f$, $u.f$, $\operatorname{Spec} \varphi$ cartesian, compatible with the group laws on points, with $g_A \circ u'.P_i = u.P_i \circ \operatorname{Spec}\varphi$ for all $i$, and with $g_A^{*}u.\mathrm{pol} \cong u'.\mathrm{pol}$; `Iso u u'` asserts the existence of an isomorphism $e \colon u.A \cong u'.A$ over $S$, a homomorphism on points, carrying each $u.P_i$ to $u'.P_i$, and with $e^{*}u'.\mathrm{pol} \cong u.\mathrm{pol}$ after restriction to $u.f^{-1}(U)$ for some open $U$ around each point of $\operatorname{Spec} S$. The theorem is the conjunction of eight assertions, for all rings and objects as indicated: `IsPullback` holds for the identity of $S$ and any $u$ with itself; it composes, i.e. `IsPullback φ u u'` and `IsPullback ψ u' u''` give `IsPullback (ψ.comp φ) u u''`; it cancels on the left, i.e. `IsPullback φ u u'` and `IsPullback (ψ.comp φ) u u''` give `IsPullback ψ u' u''`; two base changes $u'_1$, $u'_2$ of the same $u$ along the same $\varphi$ satisfy `IsPullback (RingHom.id S') u'₁ u'₂`; `IsPullback (RingHom.id S) u u'` implies `Iso u u'`; and `Iso` is reflexive, symmetric and transitive on objects over a fixed $S$.
--
--   These are the bookkeeping laws — reflexivity, composition and left cancellation of base change, uniqueness of a base change up to the identity base change, and the equivalence-relation properties of isomorphism — that make $S \mapsto$ (polarised abelian schemes of invariants $g$, $d$, $n$ over $S$) behave like a moduli problem. They are used in the construction of fine moduli data for this problem, in [`AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_of_isFineModuli_of_isPullback_of_faithfullyFlat_of_iso`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_of_isFineModuli_of_isPullback_of_faithfullyFlat_of_iso).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_isPullback_refl_comp_cancel_iso_symm_trans.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.PolarisedAbelianScheme

universe u

theorem AlgebraicGeometry.PolarisedAbelianScheme.isPullback_refl_comp_cancel_iso_symm_trans (g d n : ℕ) :
    (∀ (S : Type u) [CommRing S] (u : PolarisedAbelianScheme g d n S),
        PolarisedAbelianScheme.IsPullback (RingHom.id S) u u) ∧
    (∀ (S S' S'' : Type u) [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'')
        (u : PolarisedAbelianScheme g d n S) (u' : PolarisedAbelianScheme g d n S')
        (u'' : PolarisedAbelianScheme g d n S''),
        PolarisedAbelianScheme.IsPullback φ u u' → PolarisedAbelianScheme.IsPullback ψ u' u'' →
          PolarisedAbelianScheme.IsPullback (ψ.comp φ) u u'') ∧
    (∀ (S S' S'' : Type u) [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'')
        (u : PolarisedAbelianScheme g d n S) (u' : PolarisedAbelianScheme g d n S')
        (u'' : PolarisedAbelianScheme g d n S''),
        PolarisedAbelianScheme.IsPullback φ u u' → PolarisedAbelianScheme.IsPullback (ψ.comp φ) u u'' →
          PolarisedAbelianScheme.IsPullback ψ u' u'') ∧
    (∀ (S S' : Type u) [CommRing S] [CommRing S'] (φ : S →+* S')
        (u : PolarisedAbelianScheme g d n S) (u'₁ u'₂ : PolarisedAbelianScheme g d n S'),
        PolarisedAbelianScheme.IsPullback φ u u'₁ → PolarisedAbelianScheme.IsPullback φ u u'₂ →
          PolarisedAbelianScheme.IsPullback (RingHom.id S') u'₁ u'₂) ∧
    (∀ (S : Type u) [CommRing S] (u u' : PolarisedAbelianScheme g d n S),
        PolarisedAbelianScheme.IsPullback (RingHom.id S) u u' → PolarisedAbelianScheme.Iso u u') ∧
    (∀ (S : Type u) [CommRing S] (u : PolarisedAbelianScheme g d n S), PolarisedAbelianScheme.Iso u u) ∧
    (∀ (S : Type u) [CommRing S] (u u' : PolarisedAbelianScheme g d n S),
        PolarisedAbelianScheme.Iso u u' → PolarisedAbelianScheme.Iso u' u) ∧
    (∀ (S : Type u) [CommRing S] (u u' u'' : PolarisedAbelianScheme g d n S),
        PolarisedAbelianScheme.Iso u u' → PolarisedAbelianScheme.Iso u' u'' → PolarisedAbelianScheme.Iso u u'') := by sorry
