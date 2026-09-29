-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_mumfordBundle_pullback_diagonal_iso_tensor_of_symmetric_of_birigidified
-- name    : AlgebraicGeometry.Polarisation.nonempty_mumfordBundle_pullback_diagonal_iso_tensor_of_symmetric_of_birigidified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/cc2e96d7-d6d6-549e-a47d-3ca5b350803f
-- title:
--   Mumford bundle of a diagonal-restricted symmetric birigidified bundle
-- statement:
--   Let $k$ be an algebraically closed field, let $f : A \to \operatorname{Spec} k$ be a morphism of schemes, and let $L$ be a relative group law for $f$, i.e. a functorial group structure (multiplication, unit, inverse, with associativity, the unit laws, left inverses, and naturality under base change $T' \to T$) on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of sections over arbitrary $k$-schemes $t : T \to \operatorname{Spec} k$; assume $L$ is commutative, and assume the bundle of properties `AbelianSchemePropertyBundle` for $f$, namely that $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $g : \mathbb{N}$ be such that every fibre of $f$ has topological Krull dimension $g$. Let $\mathcal P$ be a module on $A \times_k A$ which is invertible, in the sense that every point has an open neighbourhood $U$ with $\mathcal P|_U$ isomorphic to the unit sheaf of modules on $U$. Write $\sigma$ for the symmetry automorphism of $A \times_k A$ interchanging the two factors, and let $\iota : A \times_k \operatorname{Spec} k \to A \times_k A$ be the slice morphism $(\mathrm{pr}_1, \mathrm{pr}_2 \circ e)$ attached to the identity section $e$, the zero of the group $L.\mathrm{AlgPoints}$ of $k$-points. Assume that $\iota^*\mathcal P$ and $\iota^*\sigma^*\mathcal P$ are each isomorphic to the monoidal unit, and that $\sigma^*\mathcal P \cong \mathcal P$. Then the Mumford bundle of the pullback of $\mathcal P$ along the diagonal $\Delta = \langle \mathrm{id}_A, \mathrm{id}_A\rangle : A \to A \times_k A$, that is $m^*(\Delta^*\mathcal P) \otimes \bigl(\mathrm{pr}_1^*(\Delta^*\mathcal P)^\vee \otimes \mathrm{pr}_2^*(\Delta^*\mathcal P)^\vee\bigr)$ with $m$ the addition morphism $A \times_k A \to A$ determined by $L$ and $(-)^\vee$ the internal hom into the unit, is isomorphic to $\mathcal P \otimes \mathcal P$; the conclusion asserts that the type of such isomorphisms is nonempty.
--
--   This is Mumford's computation of the Mumford (theta) bundle $\Lambda(\Delta^*\mathcal P)$ of the diagonal restriction of a symmetric birigidified line bundle on $A \times A$: biadditivity in each variable together with symmetry gives $\Lambda(\Delta^*\mathcal P) \cong \mathcal P^{\otimes 2}$. It is used, together with a halving argument, by [`AlgebraicGeometry.Polarisation.exists_nonempty_iso_mumfordBundle_of_symmetric_of_birigidified_of_two_ne_zero`](thm.html#AlgebraicGeometry.Polarisation.exists_nonempty_iso_mumfordBundle_of_symmetric_of_birigidified_of_two_ne_zero) in the identification of symmetric birigidified bundles with Mumford bundles of line bundles on $A$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_mumfordBundle_pullback_diagonal_iso_tensor_of_symmetric_of_birigidified.lean

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

theorem AlgebraicGeometry.Polarisation.nonempty_mumfordBundle_pullback_diagonal_iso_tensor_of_symmetric_of_birigidified
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (𝓟 : (pullback f f).Modules) (h𝓟 : Scheme.Modules.IsInvertible 𝓟)
    (h₁ : Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj 𝓟 ≅ 𝟙_ _))
    (h₂ : Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj
        ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj 𝓟) ≅ 𝟙_ _))
    (h₃ : Nonempty ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj 𝓟 ≅ 𝓟)) :
    Nonempty (mumfordBundle f L ((Scheme.Modules.pullback (pullback.lift (𝟙 A) (𝟙 A) rfl)).obj 𝓟) ≅ 𝓟 ⊗ 𝓟) := by sorry
