-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_isLevelPairingValue_of_isScalarElt_commutatorElement_levelLift
-- name    : AlgebraicGeometry.RiemannForm.thetaGroup.isLevelPairingValue_of_isScalarElt_commutatorElement_levelLift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/9f756ed1-ac5a-508e-9efc-a88157578150
-- title:
--   Commutator with the level lift computes the level pairing
-- statement:
--   Let $k$ be a field, $A$ a scheme with a structure morphism $f : A \to \operatorname{Spec} k$, and $L$ a relative group law on $f$ (a functorial group structure on the sets $\mathrm{SchemeHomOver}\,t\,f$ of morphisms over $\operatorname{Spec} k$), assumed commutative by $hc$. Let $\mathcal L$ be an $\mathcal O_A$-module, $n$ a natural number, $P$ a $k$-point of $L$, $c \in k$, and assume $hx$: the translation $T_P$ attached to $P$ satisfies $T_P$ followed by $[n] = L.\mathrm{schemeNsmul}\,n$ equal to $[n]$. Write $M := [n]^{*}\mathcal L$ and let $\tilde P := \mathrm{levelLift}\,f\,L\,hc\,\mathcal L\,n\,P\,hx$ be the element of the theta group $\mathcal G(M)$ — the subgroup of pairs (automorphism of the module pair $(A,M)$, $k$-point $Q$ written multiplicatively) whose underlying automorphism has base morphism $T_Q$ — obtained from $P$ together with the transport isomorphism supplied by $hx$. Then two assertions hold. First, for every $g \in \mathcal G(M)$: if the commutator $\lceil \tilde P, g \rceil = \tilde P g \tilde P^{-1} g^{-1}$ is a scalar element with value $c$, meaning its point component is trivial and the resulting automorphism of $M$ acts on sections over each open $U$ as multiplication by the image of $c$ under $k \to \Gamma(A,\mathcal O_A) \to \Gamma(U,\mathcal O_A)$, then $\mathrm{IsLevelPairingValue}\,f\,L\,\mathcal L\,n$ holds at the points $P$ and $n \cdot \mathrm{pt}(g)$ with value $c$; that is, there are a proof that $T_P$ followed by $[n]$ equals $[n]$ and an isomorphism $\beta : [n]^{*}T_{n\,\mathrm{pt}(g)}^{*}\mathcal L \cong [n]^{*}\mathcal L$ for which the composite $\beta^{-1}$, the inverse transport isomorphism, the pullback of $\beta$ along $T_P$, and the transport isomorphism for $\mathcal L$ is multiplication by the constant $c$. Second, conversely, for every $k$-point $Q_1$ with $\mathrm{IsLevelPairingValue}\,f\,L\,\mathcal L\,n$ holding at $P$ and $n Q_1$ with value $c$, there exists $g \in \mathcal G(M)$ whose point component is $Q_1$ and for which $\lceil \tilde P, g \rceil$ is a scalar element with value $c$.
--
--   This is the theta-group description of the level-$n$ pairing: the commutator of a point's canonical lift to the theta group of $[n]^{*}\mathcal L$ with an arbitrary theta-group element computes the pairing value, in both directions. It is used in the development of the Riemann form to prove bimultiplicativity of the pairing, its alternating behaviour, and a variant for isomorphisms between tensor powers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_thetaGroup_isLevelPairingValue_of_isScalarElt_commutatorElement_levelLift.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_AlgebraicGeometry_ThetaGroup
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm
open scoped commutatorElement

theorem AlgebraicGeometry.RiemannForm.thetaGroup.isLevelPairingValue_of_isScalarElt_commutatorElement_levelLift
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (𝓛 : A.Modules) (n : ℕ) (P : L.AlgPoints hc k)
    (hx : translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ L.schemeNsmul n = L.schemeNsmul n) (c : k) :
    (∀ g : thetaGroup f L hc ((Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓛),
      thetaGroup.IsScalarElt f L hc _ ⁅levelLift f L hc 𝓛 n P hx, g⁆ c →
        IsLevelPairingValue f L 𝓛 n (RelativeGroupLaw.AlgPoints.toPoint P)
          (RelativeGroupLaw.AlgPoints.toPoint (n • Multiplicative.toAdd (thetaGroup.pt f L hc _ g))) c) ∧
    (∀ Q₁ : L.AlgPoints hc k,
      IsLevelPairingValue f L 𝓛 n (RelativeGroupLaw.AlgPoints.toPoint P) (RelativeGroupLaw.AlgPoints.toPoint (n • Q₁)) c →
        ∃ g : thetaGroup f L hc ((Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓛),
          thetaGroup.pt f L hc _ g = Multiplicative.ofAdd Q₁ ∧
            thetaGroup.IsScalarElt f L hc _ ⁅levelLift f L hc 𝓛 n P hx, g⁆ c) := by sorry
