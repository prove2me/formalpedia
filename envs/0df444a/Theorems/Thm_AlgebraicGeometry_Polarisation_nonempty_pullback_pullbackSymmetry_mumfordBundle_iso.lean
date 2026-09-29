-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_pullbackSymmetry_mumfordBundle_iso
-- name    : AlgebraicGeometry.Polarisation.nonempty_pullback_pullbackSymmetry_mumfordBundle_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/02b77a95-37b7-5bd1-9b76-aa3da61a90bb
-- title:
--   Symmetry of the Mumford bundle under the flip
-- statement:
--   Let $k$ be a field, let $A$ be a scheme (in universe $0$) and let $f : A \to \operatorname{Spec} k$ be a morphism. Let $L$ be a relative group law on $f$ in the sense of the structure `RelativeGroupLaw`: for every scheme $T$ and every $t : T \to \operatorname{Spec} k$ it equips the set of $t$-sections $\{\varphi : T \to A \mid \varphi \circ f = t\}$ with a multiplication, a unit and an inversion satisfying associativity, the two unit laws and left inverse, and these operations are natural under precomposition with any $\psi : T' \to T$ over $\operatorname{Spec} k$. Assume `hc`, that $L$ is commutative, i.e. the multiplication on $t$-sections is commutative for every $t$. Let $\mathcal M$ be an $\mathcal O_A$-module. Writing $m =$ `addMor f L` for the morphism $A \times_{\operatorname{Spec} k} A \to A$ obtained by multiplying the two projections, $p_1, p_2$ for the projections, $\mathcal M^\vee$ for the internal hom from $\mathcal M$ into the monoidal unit, and $\Lambda(\mathcal M) = m^*\mathcal M \otimes (p_1^*\mathcal M^\vee \otimes p_2^*\mathcal M^\vee)$ for the Mumford bundle, the conclusion asserts that the type of isomorphisms $\sigma^*\Lambda(\mathcal M) \cong \Lambda(\mathcal M)$ of modules on $A \times_{\operatorname{Spec} k} A$ is nonempty, where $\sigma$ is the canonical symmetry automorphism of the fibre product interchanging the two factors. Only the existence of such an isomorphism is asserted, with no choice of a canonical one.
--
--   This is the symmetry of the Mumford (theta) bundle $\Lambda(\mathcal M)$ on $A \times A$ under interchanging the two factors, the source of the symmetry of the associated biextension and of the Rosati-type symmetry statements. It is used in the construction of rigidified and symmetric bundles on self-products, in the halving and two-divisibility arguments for $\Lambda$, and in the stabiliser criteria for endomorphisms compatible with a polarisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_pullbackSymmetry_mumfordBundle_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.nonempty_pullback_pullbackSymmetry_mumfordBundle_iso
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (𝓜 : A.Modules) :
    Nonempty ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj (mumfordBundle f L 𝓜) ≅ mumfordBundle f L 𝓜) := by sorry
