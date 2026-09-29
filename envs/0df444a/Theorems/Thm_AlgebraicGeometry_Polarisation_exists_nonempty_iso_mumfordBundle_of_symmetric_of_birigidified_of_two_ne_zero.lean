-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_nonempty_iso_mumfordBundle_of_symmetric_of_birigidified_of_two_ne_zero
-- name    : AlgebraicGeometry.Polarisation.exists_nonempty_iso_mumfordBundle_of_symmetric_of_birigidified_of_two_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/bfc2d02c-695e-5a55-bd2d-844b5356462d
-- title:
--   Symmetric bi-rigidified line bundles on A× A are Mumford bundles
-- statement:
--   Let $k$ be an algebraically closed field and $f : A \to \operatorname{Spec} k$ a morphism of schemes equipped with a relative group law $L$ (a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} k$, natural in $T$), assumed commutative, and assume the property bundle `AbelianSchemePropertyBundle k f`, i.e. $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and a relative group law exists. Let $g$ be a natural number such that every fibre of $f$ has topological Krull dimension $g$, and suppose $2 \neq 0$ in $k$. Let $\mathcal{P}$ be a module on $A \times_{\operatorname{Spec} k} A$ which is invertible, in the sense that every point has an open neighbourhood $U$ with $\mathcal{P}|_U$ isomorphic to the unit module on $U$. Assume: (i) the pullback of $\mathcal{P}$ along $\operatorname{sliceAt}$ at the zero point of $L$ — the map $A \times_{\operatorname{Spec} k} \operatorname{Spec} k \to A \times A$ with components $\mathrm{pr}_1$ and $\mathrm{pr}_2$ followed by the unit section, so the slice $A \times \{e\}$ — is isomorphic to the unit module; (ii) the same holds for the pullback of $\mathcal{P}$ along the symmetry of $A \times A$; (iii) the pullback of $\mathcal{P}$ along the symmetry is isomorphic to $\mathcal{P}$. Then there is an invertible module $\mathcal{M}$ on $A$ with $\mathcal{P}$ isomorphic to the Mumford bundle $\operatorname{mumfordBundle} f L\, \mathcal{M} = m^*\mathcal{M} \otimes (\mathrm{pr}_1^*\mathcal{M}^\vee \otimes \mathrm{pr}_2^*\mathcal{M}^\vee)$, where $m$ is the addition morphism of $L$.
--
--   This is the classical statement that over an algebraically closed field of characteristic other than $2$ every symmetric line bundle on $A \times A$ that is trivial along both axes is of the form $\Lambda(\mathcal{M}) = m^*\mathcal{M} \otimes \mathrm{pr}_1^*\mathcal{M}^\vee \otimes \mathrm{pr}_2^*\mathcal{M}^\vee$, i.e. that a symmetric homomorphism $A \to \widehat{A}$ is $\varphi_{\mathcal{M}}$ for some $\mathcal{M}$. It is used in the construction of Riemann forms, in [`AlgebraicGeometry.RiemannForm.exists_iso_tensorPow_tensor_of_forall_dvd_of_two_ne_zero`](thm.html#AlgebraicGeometry.RiemannForm.exists_iso_tensorPow_tensor_of_forall_dvd_of_two_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_nonempty_iso_mumfordBundle_of_symmetric_of_birigidified_of_two_ne_zero.lean

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

theorem AlgebraicGeometry.Polarisation.exists_nonempty_iso_mumfordBundle_of_symmetric_of_birigidified_of_two_ne_zero
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (h2 : (2 : k) ≠ 0)
    (𝓟 : (pullback f f).Modules) (h𝓟 : Scheme.Modules.IsInvertible 𝓟)
    (h₁ : Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj 𝓟 ≅ 𝟙_ _))
    (h₂ : Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj
        ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj 𝓟) ≅ 𝟙_ _))
    (h₃ : Nonempty ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj 𝓟 ≅ 𝓟)) :
    ∃ 𝓜 : A.Modules, Scheme.Modules.IsInvertible 𝓜 ∧ Nonempty (𝓟 ≅ mumfordBundle f L 𝓜) := by sorry
