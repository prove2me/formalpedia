-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_schemeHomOverNpow_eq_schemeHomOverId_of_isIso_of_pullback_pol_iso_of_isAlgClosed
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_schemeHomOverNpow_eq_schemeHomOverId_of_isIso_of_pullback_pol_iso_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/17efee8d-8d7a-5d34-be68-a9b03f7f2bd4
-- title:
--   Polarised abelian variety: automorphisms have finite order
-- statement:
--   Let $g, d, n$ be natural numbers and let $k$ be an algebraically closed field (in universe $0$). Let $u$ be a polarised abelian scheme of type $(g,d,n)$ over $k$, that is: a scheme $u.A$ with a structure morphism $u.f : u.A \to \operatorname{Spec} k$, a relative group law $u.L$ on the functor of points of $u.f$ which is commutative, the property bundle asserting that $u.f$ is smooth, proper, with connected fibres and admitting a group law, fibres of topological Krull dimension $g$, a family $u.P$ of $2g$ sections killed by $n$ which, over every algebraically closed field, freely generates the $n$-torsion in the sense of the independence and spanning clauses, and a module $u.\mathrm{pol}$ on $u.A$ which is invertible, defines a closed immersion into projective space by its sections relative to $u.f$, and has geometric fibre $H^0$-rank $d$. Let $\sigma$ be a morphism $u.A \to u.A$ over $\operatorname{Spec} k$ (i.e. a pair consisting of $\sigma.1 : u.A \to u.A$ together with $\sigma.1$ followed by $u.f$ being $u.f$) such that $\sigma.1$ is an isomorphism, such that $\sigma$ is a homomorphism for the group law: for every scheme $T$ over $\operatorname{Spec} k$ and all $T$-points $x, y$ of $u.f$, composing $u.L.\mathrm{mul}$ of $x$ and $y$ with $\sigma$ equals the product of $x \circ \sigma$ and $y \circ \sigma$; and such that the polarisation is locally preserved: every point $s$ of $\operatorname{Spec} k$ has an open neighbourhood $U$ for which the restrictions to $u.f^{-1}(U)$ of $\sigma.1^{*}(u.\mathrm{pol})$ and of $u.\mathrm{pol}$ are isomorphic. Then there exists $m \neq 0$ with the $m$-fold iterate of $\sigma$ (the iteration starting from the identity of $u.f$) equal to the identity morphism over $u.f$.
--
--   This is the classical finiteness of the automorphism group of a polarised abelian variety over an algebraically closed field, in the form that every automorphism preserving the group law and the polarisation class has finite order. It serves as the fibrewise input for the corresponding statement over a general base, and thence for the rigidity and separatedness properties of the moduli of polarised abelian schemes with level structure used in the project.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_schemeHomOverNpow_eq_schemeHomOverId_of_isIso_of_pullback_pol_iso_of_isAlgClosed.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_schemeHomOverNpow_eq_schemeHomOverId_of_isIso_of_pullback_pol_iso_of_isAlgClosed
    {g d n : ℕ} {k : Type} [Field k] [IsAlgClosed k] (u : PolarisedAbelianScheme g d n k)
    (σ : SchemeHomOver u.f u.f) (hσiso : IsIso σ.1)
    (hσ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t u.f),
      NeronModelInfra.schemeHomOverComp (u.L.mul t x y) σ =
        u.L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ))
    (hpol : ∀ s : ↥(Spec (CommRingCat.of k)), ∃ U : (Spec (CommRingCat.of k)).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (u.f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback σ.1).obj u.pol) ≅
        (Scheme.Modules.pullback (u.f ⁻¹ᵁ U).ι).obj u.pol)) :
    ∃ m : ℕ, m ≠ 0 ∧ NeronModelInfra.schemeHomOverNpow σ m = NeronModelInfra.schemeHomOverId u.f := by sorry
