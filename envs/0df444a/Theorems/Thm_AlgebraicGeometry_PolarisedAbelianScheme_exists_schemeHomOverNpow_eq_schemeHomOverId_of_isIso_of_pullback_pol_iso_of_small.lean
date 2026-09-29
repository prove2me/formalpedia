-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_schemeHomOverNpow_eq_schemeHomOverId_of_isIso_of_pullback_pol_iso_of_small
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_schemeHomOverNpow_eq_schemeHomOverId_of_isIso_of_pullback_pol_iso_of_small
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/bfdebc0e-5925-5cda-98e6-9f7a69e85188
-- title:
--   Polarisation-preserving automorphisms of a polarised abelian scheme are torsion
-- statement:
--   Fix natural numbers $g$, $d$, $n$ and a commutative ring $S$ (in universe $0$), and let $u$ be a polarised abelian scheme of type $(g,d,n)$ over $S$: a scheme $u.A$ with a structure morphism $u.f : u.A \to \operatorname{Spec} S$, a commutative relative group law $u.L$ on the functor of $T$-points over $\operatorname{Spec} S$, the bundle of properties that $u.f$ is smooth and proper with connected fibres and admits a relative group law, all fibres of topological Krull dimension $g$, a family $u.P$ of $2g$ sections which are $n$-torsion and which, on every geometric fibre, are independent and generate the $n$-torsion, together with a module $u.pol$ on $u.A$ that is invertible, defines a closed immersion into projective space via its sections, and has geometric fibrewise $H^0$-rank $d$. Let $\sigma$ be a morphism $u.A \to u.A$ with $\sigma \circ u.f$-compatibility $\sigma \mathbin{;} u.f = u.f$, assume its underlying morphism `σ.1` is an isomorphism, assume $\sigma$ is a homomorphism for the group law in the sense that for every scheme $T$, every $t : T \to \operatorname{Spec} S$ and all $T$-points $x,y$ of $u.A$ over $t$ one has $(x \cdot y) \mathbin{;} \sigma = (x \mathbin{;} \sigma)\cdot(y \mathbin{;} \sigma)$, and assume that $\sigma$ preserves the polarisation locally on the base: every point $s$ of $\operatorname{Spec} S$ has an open neighbourhood $U$ such that the restrictions to $u.f^{-1}U$ of $\sigma^{*}u.pol$ and of $u.pol$ are isomorphic as modules. Then there exists $m \neq 0$ with $\sigma^{m} = \mathrm{id}_{u.A}$, the power being the iterated composite $\sigma^{0} = \mathrm{id}$, $\sigma^{i+1} = \sigma^{i}$ followed by $\sigma$, in the category of $\operatorname{Spec} S$-morphisms $u.A \to u.A$.
--
--   This is the statement that an automorphism of a polarised abelian scheme respecting the group law and, locally on the base, the polarisation class has finite order — the finiteness of the automorphism group of a polarised abelian variety on geometric fibres, propagated to an arbitrary affine base. It feeds the rigidity statements for the level-$n$ moduli problem, [`AlgebraicGeometry.PolarisedAbelianScheme.eq_of_isPullback_of_isPullback_of_three_le`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.eq_of_isPullback_of_isPullback_of_three_le) and its local variant, where torsion order combines with the absence of nontrivial automorphisms fixing the level structure for $n \ge 3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_schemeHomOverNpow_eq_schemeHomOverId_of_isIso_of_pullback_pol_iso_of_small.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_schemeHomOverNpow_eq_schemeHomOverId_of_isIso_of_pullback_pol_iso_of_small
    {g d n : ℕ} {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    (σ : SchemeHomOver u.f u.f) (hσiso : IsIso σ.1)
    (hσ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t u.f),
      NeronModelInfra.schemeHomOverComp (u.L.mul t x y) σ =
        u.L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ))
    (hpol : ∀ s : ↥(Spec (CommRingCat.of S)), ∃ U : (Spec (CommRingCat.of S)).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (u.f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback σ.1).obj u.pol) ≅
        (Scheme.Modules.pullback (u.f ⁻¹ᵁ U).ι).obj u.pol)) :
    ∃ m : ℕ, m ≠ 0 ∧ NeronModelInfra.schemeHomOverNpow σ m = NeronModelInfra.schemeHomOverId u.f := by sorry
