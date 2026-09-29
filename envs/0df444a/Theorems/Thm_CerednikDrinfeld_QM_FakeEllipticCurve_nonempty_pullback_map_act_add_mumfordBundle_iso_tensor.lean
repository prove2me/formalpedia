-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_pullback_map_act_add_mumfordBundle_iso_tensor
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_pullback_map_act_add_mumfordBundle_iso_tensor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/97ef0d0f-3a86-5e5f-b48f-66ee759e6445
-- title:
--   Biadditivity of the Mumford bundle under the Λ-action
-- statement:
--   Let $a,b$ be rationals, $\Lambda$ a $\mathbb{Z}$-submodule of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, $N$ a natural number, and $k$ an algebraically closed field. Let $E$ be a fake elliptic curve of level data $(\Lambda,N)$ over $k$: in particular a scheme $E.A$ with structure morphism $E.f : E.A \to \operatorname{Spec} k$, a relative group law $E.L$ on $E.f$ which is commutative, the property bundle $E.\mathrm{bundle}$ (smoothness, properness, connected fibres, existence of a relative group law), two-dimensional fibres, and for each $x \in \Lambda$ an endomorphism $E.\mathrm{act}\,x$ of $E.A$ over $E.f$, these endomorphisms being additive on points both in the argument and in $x$, multiplicative for products in $\Lambda$, unital, and of the prescribed trace. Let $\mathcal{L}$ be a module on $E.A$ which is invertible, i.e. every point has an open neighbourhood $U$ such that the restriction of $\mathcal{L}$ to $U$ is isomorphic to the unit sheaf of modules on $U$. Write $\Lambda(\mathcal{L}) = \mathrm{mumfordBundle}\ E.f\ E.L\ \mathcal{L}$ for the module $m^{*}\mathcal{L} \otimes (p_1^{*}\mathcal{L}^{\vee} \otimes p_2^{*}\mathcal{L}^{\vee})$ on $E.A \times_{\operatorname{Spec} k} E.A$, where $m$ is the addition morphism attached to $E.L$, $p_1,p_2$ are the two projections, and $\mathcal{L}^{\vee}$ is the internal hom from $\mathcal{L}$ into the unit; and for $y,z \in \Lambda$ let $\Phi(y,z)$ be the pullback of $\Lambda(\mathcal{L})$ along the product morphism $E.\mathrm{act}\,y \times E.\mathrm{act}\,z$ of $E.A \times_{\operatorname{Spec} k} E.A$, formed as `pullback.map` of $E.f,E.f,E.f,E.f$ with components $E.\mathrm{act}\,y$, $E.\mathrm{act}\,z$ and the identity of $\operatorname{Spec} k$. The theorem asserts the conjunction of two statements: for all $y,y',z \in \Lambda$ there exists an isomorphism $\Phi(y+y',z) \cong \Phi(y,z) \otimes \Phi(y',z)$, and for all $y,z,z' \in \Lambda$ there exists an isomorphism $\Phi(y,z+z') \cong \Phi(y,z) \otimes \Phi(y,z')$; the isomorphisms are asserted only as nonemptiness of the respective types, with no compatibility between them.
--
--   This is the biadditivity, up to isomorphism of invertible sheaves, of the symbol $(y,z) \mapsto (\iota y \times \iota z)^{*}\Lambda(\mathcal{L})$ attached to an invertible sheaf on a fake elliptic curve over an algebraically closed field; it is a consequence of the theorem of the cube together with the additivity of the quaternionic action on points. It feeds the construction of a Rosati-compatible polarisation on fake elliptic curves, being cited by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_finiteBySections_rosatiCompatible_of_isAlgClosed`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_finiteBySections_rosatiCompatible_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_pullback_map_act_add_mumfordBundle_iso_tensor.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_pullback_map_act_add_mumfordBundle_iso_tensor
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (k : Type) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k)
    (𝓛 : E.A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) :
    (∀ y y' z : ↥Λ, Nonempty
      ((Scheme.Modules.pullback (pullback.map E.f E.f E.f E.f (E.act (y + y')) (E.act z) (𝟙 _)
          (by rw [Category.comp_id, E.act_over]) (by rw [Category.comp_id, E.act_over]))).obj (mumfordBundle E.f E.L 𝓛) ≅
        (Scheme.Modules.pullback (pullback.map E.f E.f E.f E.f (E.act y) (E.act z) (𝟙 _)
          (by rw [Category.comp_id, E.act_over]) (by rw [Category.comp_id, E.act_over]))).obj (mumfordBundle E.f E.L 𝓛) ⊗
        (Scheme.Modules.pullback (pullback.map E.f E.f E.f E.f (E.act y') (E.act z) (𝟙 _)
          (by rw [Category.comp_id, E.act_over]) (by rw [Category.comp_id, E.act_over]))).obj (mumfordBundle E.f E.L 𝓛))) ∧
    (∀ y z z' : ↥Λ, Nonempty
      ((Scheme.Modules.pullback (pullback.map E.f E.f E.f E.f (E.act y) (E.act (z + z')) (𝟙 _)
          (by rw [Category.comp_id, E.act_over]) (by rw [Category.comp_id, E.act_over]))).obj (mumfordBundle E.f E.L 𝓛) ≅
        (Scheme.Modules.pullback (pullback.map E.f E.f E.f E.f (E.act y) (E.act z) (𝟙 _)
          (by rw [Category.comp_id, E.act_over]) (by rw [Category.comp_id, E.act_over]))).obj (mumfordBundle E.f E.L 𝓛) ⊗
        (Scheme.Modules.pullback (pullback.map E.f E.f E.f E.f (E.act y) (E.act z') (𝟙 _)
          (by rw [Category.comp_id, E.act_over]) (by rw [Category.comp_id, E.act_over]))).obj (mumfordBundle E.f E.L 𝓛))) := by sorry
