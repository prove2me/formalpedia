-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_ringHom_moduleEnd_forall_eq_pushPt
-- name    : CerednikDrinfeld.QM.exists_ringHom_moduleEnd_forall_eq_pushPt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/80a4bdc9-9d42-5194-91ce-50f700056fce
-- title:
--   Ring action on a relative group law differentiates to Λ → End_κ(W)
-- statement:
--   Let $\kappa$ be a field and $f_X : X \to \operatorname{Spec}\kappa$ a scheme over $\kappa$ carrying a relative group law $L$, i.e. for each $\kappa$-scheme $t : T \to \operatorname{Spec}\kappa$ a group structure (multiplication, unit, inverse, associativity, unit and inverse laws) on the set of $\varphi : T \to X$ with $\varphi$ followed by $f_X$ equal to $t$, natural in $T$. Let $W$ be a $\kappa$-vector space together with a map $\tau_W$ from $W$ to the $\kappa[\varepsilon]$-points of $X$ (points over the map $\operatorname{Spec}\kappa[\varepsilon] \to \operatorname{Spec}\kappa$ induced by $\kappa \to \kappa[\varepsilon]$) which is injective, whose image consists exactly of those points $P$ with $P$ precomposed by the zero section $\operatorname{Spec}\kappa \to \operatorname{Spec}\kappa[\varepsilon]$ equal to the unit $\kappa$-point $L.one$, which is additive for $L$'s multiplication, and for which $\tau_W(a \cdot v)$ is $\tau_W(v)$ precomposed with the scaling automorphism $\varepsilon \mapsto a\varepsilon$ of $\kappa[\varepsilon]$. Let $\Lambda$ be a ring and $\psi : \Lambda \to (X \to X)$ assign to each $x$ an endomorphism over $\kappa$ ($\psi x$ followed by $f_X$ is $f_X$) such that postcomposition by $\psi x$ respects $L$'s multiplication on $t$-points for every $t$, such that $\psi 1 = \mathrm{id}_X$, $\psi(xy) = \psi y$ followed by $\psi x$, and such that for every $t$-point $P$, $P$ followed by $\psi(x+y)$ is the $L$-product of $P$ followed by $\psi x$ and $P$ followed by $\psi y$. Then there exists a ring homomorphism $\theta_\Lambda : \Lambda \to \operatorname{End}_\kappa(W)$ with $\tau_W(\theta_\Lambda(x)\,w) = \tau_W(w)$ followed by $\psi x$, for all $x \in \Lambda$ and $w \in W$.
--
--   This is the passage from a ring action on a relative group scheme to its action on the tangent space at the unit, the differential at the identity in the sense of Mumford's discussion of abelian varieties, packaged as a single ring homomorphism into $\operatorname{End}_\kappa(W)$. It feeds the Čerednik–Drinfeld side of the argument, being used in [`GoodReductionJacobian.BareDeformation.exists_forall_exists_comp_eq_comp_of_separabilityElement_of_ker_mul_maximalIdeal_eq_bot`](thm.html#GoodReductionJacobian.BareDeformation.exists_forall_exists_comp_eq_comp_of_separabilityElement_of_ker_mul_maximalIdeal_eq_bot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_ringHom_moduleEnd_forall_eq_pushPt.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped TensorProduct

theorem CerednikDrinfeld.QM.exists_ringHom_moduleEnd_forall_eq_pushPt
    {κ : Type} [Field κ] {X : Scheme.{0}} (fX : X ⟶ Spec (CommRingCat.of κ)) (L : RelativeGroupLaw κ fX)
    (W : Type) [AddCommGroup W] [Module κ W]
    (τW : W → SchemeHomOver (tangentBase κ (RingHom.id κ)) fX)
    (hWinj : Function.Injective τW)
    (hWrange : ∀ P : SchemeHomOver (tangentBase κ (RingHom.id κ)) fX, P ∈ Set.range τW ↔ IsTangentVector L κ (RingHom.id κ) P)
    (hWadd : ∀ v w : W, τW (v + w) = L.mul (tangentBase κ (RingHom.id κ)) (τW v) (τW w))
    (hWsmul : ∀ (a : κ) (v : W), (τW (a • v)).1 = tangentScale κ a ≫ (τW v).1)
    {Λ : Type} [Ring Λ] (ψ : Λ → (X ⟶ X)) (hψ : ∀ x : Λ, ψ x ≫ fX = fX)
    (hψhom : ∀ (x : Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (P Q : SchemeHomOver t fX),
      pushPt (ψ x) (hψ x) (L.mul t P Q) = L.mul t (pushPt (ψ x) (hψ x) P) (pushPt (ψ x) (hψ x) Q))
    (hψone : ψ 1 = 𝟙 X) (hψmul : ∀ x y : Λ, ψ (x * y) = ψ y ≫ ψ x)
    (hψadd : ∀ (x y : Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (P : SchemeHomOver t fX),
      P.1 ≫ ψ (x + y) = (L.mul t ⟨P.1 ≫ ψ x, by rw [Category.assoc, hψ, P.2]⟩ ⟨P.1 ≫ ψ y, by rw [Category.assoc, hψ, P.2]⟩).1) :
    ∃ θΛ : Λ →+* Module.End κ W, ∀ (x : Λ) (w : W), τW (θΛ x w) = pushPt (ψ x) (hψ x) (τW w) := by sorry
