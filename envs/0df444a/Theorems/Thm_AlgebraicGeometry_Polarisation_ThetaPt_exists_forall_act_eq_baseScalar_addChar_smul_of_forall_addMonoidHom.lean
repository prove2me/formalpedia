-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_exists_forall_act_eq_baseScalar_addChar_smul_of_forall_addMonoidHom
-- name    : AlgebraicGeometry.Polarisation.ThetaPt.exists_forall_act_eq_baseScalar_addChar_smul_of_forall_addMonoidHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/5629adac-1f08-5aee-8c95-f3bce8cf0b3d
-- title:
--   Theta points realising arbitrary additive characters of H(δ)
-- statement:
--   Fix a commutative ring $S$, a scheme $A$ and a morphism $f : A \to \operatorname{Spec} S$, together with a relative group law $L$ on $f$, i.e. functorial group operations on the sets $\{\varphi : T \to A \mid \varphi \circ$ (structure map) $= t\}$ of $T$-points over $\operatorname{Spec} S$, compatible with base change along morphisms $T' \to T$, and a module $\mathcal{L}$ on $A$. Fix further a commutative ring $R$ and a test morphism $t : \operatorname{Spec} R \to \operatorname{Spec} S$, a natural number $N$ and $\zeta \in R$ with $\zeta^{N+1} = 1$ and $1 - \zeta^{j}$ a unit for all $0 < j < N+1$, and a tuple $\delta : \mathrm{Fin}\, g \to \mathbb{N}$ of nonzero integers together with a bijection $\mathrm{Fin}(N+1) \simeq H(\delta) := \prod_{i} \mathbb{Z}/\delta_i$ (so $|H(\delta)| = N+1$). Let $\sigma$ assign to each $h \in H(\delta)$ a global section $\sigma_h$ of the pullback of $\mathcal{L}$ along the first projection $\operatorname{pullback} f\,t \to A$, and let $\eta$ assign to each additive homomorphism $c : H(\delta) \to \mathbb{Z}/(N+1)$ a theta point $\eta_c$ over $t$ — a point of $A$ over $t$ together with an isomorphism between the pullback of $\mathrm{pr}_1^{*}\mathcal{L}$ along the translation by that point and $\mathrm{pr}_1^{*}\mathcal{L}$ itself — whose induced action satisfies $\eta_c . \sigma_h = \zeta^{(c\,h)} \cdot \sigma_h$ for all $h$, the scalar being the global function on $\operatorname{pullback} f\,t$ obtained from $\zeta^{(c\,h)} \in R$ by pulling back along the second projection, and $(c\,h)$ read as the natural-number representative of its class. Then for every additive character $\chi : H(\delta) \to R$ there exists a theta point $\theta$ over $t$ with $\theta . \sigma_h = \chi(h) \cdot \sigma_h$ for all $h \in H(\delta)$, again with $\chi(h)$ pulled back to a global function on $\operatorname{pullback} f\,t$.
--
--   This is the step in Mumford's theory of theta groups that upgrades a supply of theta points acting on a fixed family of sections through the $\zeta$-power characters $\zeta^{c}$ to one acting through an arbitrary $R$-valued additive character of $H(\delta)$; the mechanism is a decomposition of $R$ into complete orthogonal idempotents attached to $\chi$, base change of theta points to the resulting pieces, and gluing. It is used in the treatment of theta-adapted framings of polarised abelian schemes, in particular by the characterisations and stability statements for that notion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_ThetaPt_exists_forall_act_eq_baseScalar_addChar_smul_of_forall_addMonoidHom.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.ThetaPt.exists_forall_act_eq_baseScalar_addChar_smul_of_forall_addMonoidHom
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f) (𝓛 : A.Modules)
    {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (N : ℕ) (ζ : R) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    (σ : ((i : Fin g) → ZMod (δ i)) → Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤))
    (η : (((i : Fin g) → ZMod (δ i)) →+ ZMod (N + 1)) → ThetaPt f L 𝓛 t)
    (hη : ∀ (c : ((i : Fin g) → ZMod (δ i)) →+ ZMod (N + 1)) (h : (i : Fin g) → ZMod (δ i)),
      (η c).act (σ h) = Polarisation.baseScalar f t (ζ ^ (c h).val) • σ h)
    (χ : AddChar ((i : Fin g) → ZMod (δ i)) R) :
    ∃ θ : ThetaPt f L 𝓛 t, ∀ h : (i : Fin g) → ZMod (δ i), θ.act (σ h) = Polarisation.baseScalar f t (χ h) • σ h := by sorry
