-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_nonempty_tensorPow_pullback_translation_tensor_dual_iso_unit_monoidalV2
-- name    : AlgebraicGeometry.RiemannForm.nonempty_tensorPow_pullback_translation_tensor_dual_iso_unit_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/ed9296b4-9f88-5002-9973-fcf8928aef70
-- title:
--   n-torsion translation: (T_Q^*LotimesL^∨)^{⊗ n} is trivial
-- statement:
--   Let $k$ be an algebraically closed field, let $A$ be a scheme and $f : A \to \operatorname{Spec} k$ a morphism, and let $L$ be a `RelativeGroupLaw` for $f$, that is, a group structure on the sets $\mathrm{SchemeHomOver}\,t\,f$ of $T$-points of $f$ over each $t : T \to \operatorname{Spec} k$ (multiplication, unit, inverse, with associativity, unit laws, left inverse, and naturality of multiplication under base change along $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$); assume `hc`, that each of these group laws is commutative, and `hA`, the bundle asserting that $f$ is smooth, proper, has connected fibres over every point of $\operatorname{Spec} k$, and admits a relative group law. Let $\mathcal L$ be an object of `A.Modules` which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ with the pullback of $\mathcal L$ along $U.\iota$ isomorphic to the unit module on $U$. Let $n : \mathbb{N}$ and let $Q$ be an element of `L.AlgPoints hc k`, the additive group underlying the $k$-points $\mathrm{SchemeHomOver}\,(\operatorname{Spec}$ of the structure map $k \to k)\,f$, with $n \cdot Q = 0$. Then the $n$-fold tensor power (defined by $0 \mapsto \mathbf 1$, $m+1 \mapsto {\cdot}^{\otimes m} \otimes {\cdot}$) of $T_Q^{*}\mathcal L \otimes \mathcal L^{\vee}$ admits an isomorphism to the monoidal unit of `A.Modules`, where $T_Q$ is `translation f L` at the point underlying $Q$, i.e. the underlying morphism $A \to A$ of the product of the identity point with the constant point $Q$, and $\mathcal L^{\vee}$ is `Scheme.Modules.dual 𝓛`, the internal hom from $\mathcal L$ to the unit. The conclusion is stated as nonemptiness of the type of such isomorphisms.
--
--   This is the standard consequence of the theorem of the square that $\varphi_{\mathcal L} : x \mapsto T_x^{*}\mathcal L \otimes \mathcal L^{\vee}$ is a homomorphism from $A(k)$ to $\operatorname{Pic}(A)$, so that $n$-torsion points are sent to $n$-torsion classes, here in the trivialised form for a point killed by $n$. It feeds the construction of the Riemann form and Weil pairing material, being cited by [`AlgebraicGeometry.RiemannForm.nonempty_pullback_schemeNsmul_pullback_translation_iso`](thm.html#AlgebraicGeometry.RiemannForm.nonempty_pullback_schemeNsmul_pullback_translation_iso).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_nonempty_tensorPow_pullback_translation_tensor_dual_iso_unit_monoidalV2.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.nonempty_tensorPow_pullback_translation_tensor_dual_iso_unit_monoidalV2
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (n : ℕ) (Q : L.AlgPoints hc k) (hQ : n • Q = 0) :
    Nonempty (((Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))).obj 𝓛 ⊗
        Scheme.Modules.dual 𝓛).tensorPow n ≅ 𝟙_ A.Modules) := by sorry
