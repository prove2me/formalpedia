-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_isLevelPairingValue_of_isScalarElt_commutator_of_iso_tpow_tensor_tpow_negMor
-- name    : AlgebraicGeometry.RiemannForm.thetaGroup.isLevelPairingValue_of_isScalarElt_commutator_of_iso_tpow_tensor_tpow_negMor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/f225d370-448e-574a-bb67-cab8fa7ebc95
-- title:
--   Theta-group commutator as a level pairing value
-- statement:
--   Let $k$ be an algebraically closed field and $f : A \to \operatorname{Spec} k$ a morphism of schemes equipped with a relative group law $L$ (a functorial group structure on the sets $\operatorname{Hom}_{\operatorname{Spec} k}(T, A)$, natural in $T$) which is commutative, and assume the bundle $hA$: $f$ is smooth and proper, its fibres are connected, and a relative group law on $f$ exists. Let $g$ be a natural number such that every fibre of $f$ has topological Krull dimension $g$. Let $\mathcal L, \mathcal L_0$ be $\mathcal O_A$-modules, each invertible in the sense that every point of $A$ has an open neighbourhood $U$ over which the pullback along $U \hookrightarrow A$ is isomorphic to the unit sheaf of modules. Let $a, b$ be natural numbers with $a + b \ge 1$ and with $a + b$ invertible in $k$, and let $\iota$ be an isomorphism $\mathcal L \cong \mathcal L_0^{\otimes a} \otimes ([-1]^{*}\mathcal L_0)^{\otimes b}$, the tensor powers being formed by `Scheme.Modules.tpow` and $[-1]$ being the inversion morphism $A \to A$ attached to $L$ at the identity point. Let $g_1, g_2$ be elements of the theta group `thetaGroup f L hc 𝓛`, that is, pairs consisting of an automorphism of the pair $(A, \mathcal L)$ and a $k$-point of $A$, written multiplicatively, such that the automorphism lies over translation by that point; write $P, Q$ for the associated $k$-points and assume $(a+b) \cdot P = 0$ and $(a+b)\cdot Q = 0$. Let $c \in k$ be such that the commutator $\lbrack g_1, g_2 \rbrack$ is a scalar element with value $c$, i.e. its point component is trivial and the induced automorphism of $\mathcal L$ over the identity is the constant scalar $c$. Then $c$ is a level pairing value for $\mathcal L_0$ at level $a+b$ on $(P, Q)$: translation by $P$ followed by multiplication by $a+b$ equals multiplication by $a+b$, and there is an isomorphism $\beta$ from $[a+b]^{*}t_Q^{*}\mathcal L_0$ to $[a+b]^{*}\mathcal L_0$ for which the composite of $\beta^{-1}$, the inverse transport isomorphism, $t_P^{*}\beta$ and the transport isomorphism is multiplication by the constant $c$.
--
--   This is the identification of the commutator pairing on Mumford's theta group of $\mathcal L$ with the level $(a+b)$ pairing attached to $\mathcal L_0$, in the situation where $\mathcal L$ is an $(a,b)$-mixture $\mathcal L_0^{\otimes a} \otimes ([-1]^{*}\mathcal L_0)^{\otimes b}$. It feeds the nondegeneracy step [`AlgebraicGeometry.PolarisedAbelianScheme.thetaPt_pt_eq_one_of_forall_act_comm_of_principalRoot_of_ne_zero`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.thetaPt_pt_eq_one_of_forall_act_comm_of_principalRoot_of_ne_zero), where an element commuting with all theta-group elements is shown to lie over the identity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_thetaGroup_isLevelPairingValue_of_isScalarElt_commutator_of_iso_tpow_tensor_tpow_negMor.lean

import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_AlgebraicGeometry_ThetaGroup
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm MonoidalCategory
open scoped commutatorElement

theorem AlgebraicGeometry.RiemannForm.thetaGroup.isLevelPairingValue_of_isScalarElt_commutator_of_iso_tpow_tensor_tpow_negMor
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (𝓛 𝓛₀ : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀)
    (a b : ℕ) (hab : 1 ≤ a + b) (hm : ((a + b : ℕ) : k) ≠ 0)
    (ι : 𝓛 ≅ Scheme.Modules.tpow 𝓛₀ a ⊗ Scheme.Modules.tpow ((Scheme.Modules.pullback (Polarisation.negMor f L)).obj 𝓛₀) b)
    (g₁ g₂ : thetaGroup f L hc 𝓛)
    (hP : (a + b) • Multiplicative.toAdd (thetaGroup.pt f L hc 𝓛 g₁) = 0)
    (hQ : (a + b) • Multiplicative.toAdd (thetaGroup.pt f L hc 𝓛 g₂) = 0)
    (c : k) (h : thetaGroup.IsScalarElt f L hc 𝓛 ⁅g₁, g₂⁆ c) :
    IsLevelPairingValue f L 𝓛₀ (a + b)
      (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd (thetaGroup.pt f L hc 𝓛 g₁)))
      (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd (thetaGroup.pt f L hc 𝓛 g₂))) c := by sorry
