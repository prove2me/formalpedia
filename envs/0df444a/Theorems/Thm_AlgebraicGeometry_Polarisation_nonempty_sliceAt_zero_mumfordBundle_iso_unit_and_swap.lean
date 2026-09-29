-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_sliceAt_zero_mumfordBundle_iso_unit_and_swap
-- name    : AlgebraicGeometry.Polarisation.nonempty_sliceAt_zero_mumfordBundle_iso_unit_and_swap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/a8119414-9c0e-5812-b0f6-48be936171a8
-- title:
--   Mumford bundle trivial along the zero slice, and after swapping
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme, and $f : A \to \operatorname{Spec} k$ a morphism, equipped with a relative group law $L$ on $f$: a functorial group structure (multiplication, unit, inverse, with associativity, both unit laws, left inverse and naturality under base change) on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $A$-points over arbitrary $t : T \to \operatorname{Spec} k$; assume $L$ is commutative, i.e. all these multiplications commute. Let $\mathcal M$ be a module on $A$ which is invertible, meaning that every point of $A$ has an open neighbourhood on which the restriction of $\mathcal M$ is isomorphic to the unit sheaf of modules. Write $\Lambda(\mathcal M) = m^*\mathcal M \otimes (p_1^*\mathcal M^\vee \otimes p_2^*\mathcal M^\vee)$ for the Mumford bundle on $A \times_{\operatorname{Spec} k} A$, where $m$ is the morphism induced by $L$ on the fibre product and $\mathcal M^\vee$ is the internal-hom dual. Let $e$ denote the zero element of the group of $k$-algebra points $\mathrm{AlgPoints}$ of $L$, and let $\mathrm{sliceAt}$ denote the induced morphism $A \times_{\operatorname{Spec} k} \operatorname{Spec} k \to A \times_{\operatorname{Spec} k} A$ with components $p_1$ and $p_2$ followed by $e$. The assertion is that both the pullback of $\Lambda(\mathcal M)$ along this slice and the pullback of $\sigma^*\Lambda(\mathcal M)$ along it, where $\sigma$ is the canonical symmetry of the fibre product, admit isomorphisms to the unit object of the monoidal category of modules on the source.
--
--   This is the birigidification of the Mumford bundle: $\Lambda(\mathcal M)$ is trivial along $A \times \{e\}$ and, by symmetry, along $\{e\} \times A$. It supplies the normalisation hypotheses used later when $\Lambda(\mathcal M)$ is compared with its tensor powers and with pullbacks along multiplication-by-$n$ maps, and in the identification of symmetric line bundles with polarisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_sliceAt_zero_mumfordBundle_iso_unit_and_swap.lean

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

theorem AlgebraicGeometry.Polarisation.nonempty_sliceAt_zero_mumfordBundle_iso_unit_and_swap
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (𝓜 : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) :
    Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj (mumfordBundle f L 𝓜) ≅ 𝟙_ _) ∧
    Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj
        ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj (mumfordBundle f L 𝓜)) ≅ 𝟙_ _) := by sorry
