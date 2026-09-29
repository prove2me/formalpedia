-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_exists_bijective_thetaGroup_antiHom_of_compatible
-- name    : AlgebraicGeometry.Polarisation.ThetaPt.exists_bijective_thetaGroup_antiHom_of_compatible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/040a667a-0897-5497-b526-85242cc18ccb
-- title:
--   Theta points over a field as Mumford's theta group
-- statement:
--   Fix a commutative ring $S$, a scheme $A$, a morphism $f : A \to \operatorname{Spec} S$, a relative group law $L$ on $f$ over $S$ (functorial group operations on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $t$, natural in $T$), a module $\mathcal L$ on $A$, a field $K$ and a morphism $t : \operatorname{Spec} K \to \operatorname{Spec} S$; write $\mathrm{pr}_1, \mathrm{pr}_2$ for the projections of $A_K := A \times_{\operatorname{Spec} S} \operatorname{Spec} K$. Let $L'$ be a relative group law on $\mathrm{pr}_2$ over $K$ which is commutative ($hc'$) and compatible with $L$ through $\mathrm{pr}_1$ ($hL'$): for every scheme $T$, every $t' : T \to \operatorname{Spec} K$ and all $T$-points $P, Q$ of $A_K$ over $t'$, the morphism underlying $L'.\mathrm{mul}\,t'\,P\,Q$ followed by $\mathrm{pr}_1$ equals the morphism underlying the $L$-product, over $t' \circ t$, of $P$ followed by $\mathrm{pr}_1$ and $Q$ followed by $\mathrm{pr}_1$. The assertion is that there exists a map $\Phi$ from the theta points of $(f, L, \mathcal L)$ at $t$ — pairs consisting of a point $\mathrm{pt} : \operatorname{Spec} K \to A$ over $t$ together with an isomorphism of the pullback of $\mathrm{pr}_1^{*}\mathcal L$ along translation by $\mathrm{pt}$ with $\mathrm{pr}_1^{*}\mathcal L$ — to the theta group of $(\mathrm{pr}_2, L', hc')$ on $\mathrm{pr}_1^{*}\mathcal L$, that is, the subgroup of pairs (automorphism of the module pair, $K$-point of $L'$) whose automorphism has base morphism the translation by that point, such that: $\Phi$ is bijective; $\Phi 1 = 1$; $\Phi$ is anti-multiplicative, $\Phi(\theta\theta') = \Phi(\theta')\Phi(\theta)$; the point component of $\Phi\theta$, followed by $\mathrm{pr}_1$, is the morphism underlying $\theta.\mathrm{pt}$; whenever the commutator $\lbrack \Phi\theta, \Phi\theta'\rbrack$ is the scalar element attached to $c \in K$ (its point component is trivial and the resulting automorphism of $\mathrm{pr}_1^{*}\mathcal L$ is multiplication by the constant $c$), the actions on global sections of $\mathrm{pr}_1^{*}\mathcal L$ satisfy $\theta.\mathrm{act}(\theta'.\mathrm{act}\,s) = \mathrm{baseScalar}(c)\cdot \theta'.\mathrm{act}(\theta.\mathrm{act}\,s)$, where $\mathrm{baseScalar}(c)$ is $c$ pulled back to $\Gamma(A_K, \mathcal O)$ along $\mathrm{pr}_2$; and for every unit $c$ of $K$, $\Phi$ of the theta point given by the homothety $c$ is the scalar element attached to $c^{-1}$.
--
--   This is the dictionary identifying theta points of $(\mathcal L, L)$ at a $K$-valued test point with Mumford's theta group of the base-changed pair $(A_K, \mathrm{pr}_1^{*}\mathcal L)$, the central extension of points by scalars, the translation orientation of the stored fibre isomorphism accounting for the anti-multiplicativity and for the scalar $c^{-1}$. It is used to transport nondegeneracy statements about the commutator pairing back to the action of theta points on sections, in particular in the proof that a theta point whose action commutes with all others has trivial underlying point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_ThetaPt_exists_bijective_thetaGroup_antiHom_of_compatible.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_ThetaGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped commutatorElement

theorem AlgebraicGeometry.Polarisation.ThetaPt.exists_bijective_thetaGroup_antiHom_of_compatible
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (𝓛 : A.Modules)
    {K : Type} [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of S))
    (L' : RelativeGroupLaw K (pullback.snd f t)) (hc' : L'.IsCommutative)
    (hL' : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t' (pullback.snd f t)),
      (L'.mul t' P Q).1 ≫ pullback.fst f t =
        (L.mul (t' ≫ t)
          ⟨P.1 ≫ pullback.fst f t, by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pullback.fst f t, by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) :
    ∃ Φ : ThetaPt f L 𝓛 t →
        RiemannForm.thetaGroup (pullback.snd f t) L' hc'
          ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛),
      Function.Bijective Φ ∧ Φ 1 = 1 ∧ (∀ θ θ' : ThetaPt f L 𝓛 t, Φ (θ * θ') = Φ θ' * Φ θ) ∧
      (∀ θ : ThetaPt f L 𝓛 t,
        (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd
          (RiemannForm.thetaGroup.pt (pullback.snd f t) L' hc' _ (Φ θ)))).1 ≫
            pullback.fst f t = θ.pt.1) ∧
      (∀ (θ θ' : ThetaPt f L 𝓛 t) (c : K),
        RiemannForm.thetaGroup.IsScalarElt (pullback.snd f t) L' hc' _ ⁅Φ θ, Φ θ'⁆ c →
          ∀ s : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤),
            θ.act (θ'.act s) = baseScalar f t c • θ'.act (θ.act s)) ∧
      (∀ c : Kˣ, RiemannForm.thetaGroup.IsScalarElt (pullback.snd f t) L' hc' _
          (Φ (ThetaPt.ofScalar c)) ((c⁻¹ : Kˣ) : K)) := by sorry
