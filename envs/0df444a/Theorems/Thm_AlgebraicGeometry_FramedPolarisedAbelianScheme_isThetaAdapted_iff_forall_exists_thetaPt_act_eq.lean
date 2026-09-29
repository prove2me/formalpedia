-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_iff_forall_exists_thetaPt_act_eq
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.isThetaAdapted_iff_forall_exists_thetaPt_act_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/d4066eda-c7fd-5cbc-855e-0c8aa511c561
-- title:
--   Theta-adaptedness via translation lifts and standard dual theta points
-- statement:
--   Fix natural numbers $g, N, n$, a tuple $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with every $\delta_i$ nonzero, and a bijection $e$ from $\mathrm{Fin}(N+1)$ onto $H(\delta) = \prod_i \mathbb{Z}/\delta_i$. Let $S$ be a commutative ring and $\zeta \in S$ an element with $\zeta^{N+1} = 1$ such that $1 - \zeta^{j}$ is a unit for all $0 < j < N+1$. Let $X$ be a framed polarised abelian scheme of type $(g, N, n)$ over $S$: a commutative relative group law $L$ on $f : A \to \operatorname{Spec} S$ with the abelian-scheme property bundle, fibres of dimension $g$, an $n$-torsion frame $P$ of $2g$ points, an invertible module $\mathrm{pol}$ with geometric fibre $H^0$-rank $N+1$ defining a closed immersion by sections, together with a projective presentation `frame` of $\mathrm{pol}$ over $f$ of degree $N$ whose map to $\mathbb{P}^N$ is a closed immersion and whose global sections $\sigma_0,\dots,\sigma_N$ form a section basis. Let $\sigma'$ assign to each $h \in H(\delta)$ a global section of the pullback of $\mathrm{pol}$ along the first projection of $A \times_{\operatorname{Spec} S} \operatorname{Spec} S$ (base change along the identity), and assume $\sigma'(e(i))$ is the pullback local section of $\sigma_i$ for every $i$. The assertion is an equivalence: $X$ is theta-adapted for $(\delta, e)$, that is, there is a Schrödinger frame for $(f, L, \mathrm{pol})$ over the identity base change with multidegree $\delta$ whose sections are the $\sigma'(e(i))$ — equivalently, sections $\sigma$, bijectivity of $c \mapsto \sum_h \mathrm{baseScalar}(c_h) \cdot \sigma_h$, a family of theta points lifting translations by $H(\delta)$ and a family lifting all additive characters of $H(\delta)$ with values in $S$, acting on the $\sigma$ by $\sigma_{h'} \mapsto \sigma_{h+h'}$ and by multiplication by the character — if and only if both of the following hold: for every $h \in H(\delta)$ there is a theta point $\theta$ (a point of $A$ over $S$ together with an isomorphism between the translate-pullback of the pulled-back $\mathrm{pol}$ and itself) with $\theta.\mathrm{act}(\sigma'(h')) = \sigma'(h+h')$ for all $h'$, and for every additive homomorphism $c : H(\delta) \to \mathbb{Z}/(N+1)$ there is a theta point $\eta$ with $\eta.\mathrm{act}(\sigma'(h)) = \mathrm{baseScalar}(\zeta^{(c\,h).\mathrm{val}}) \cdot \sigma'(h)$ for all $h$.
--
--   This reduces theta-adaptedness of a framed polarised abelian scheme — the existence of a full Schrödinger frame in the sense of Mumford's theta-group formalism, with its basis property and lifts of all translations and all additive characters — to the existence of theta points for translations by $H(\delta)$ and for the finitely many standard characters $\zeta^{c(\cdot)}$ attached to homomorphisms $H(\delta) \to \mathbb{Z}/(N+1)$. It is used in the construction of a finitely generated ideal cutting out the theta-adapted locus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_iff_forall_exists_thetaPt_act_eq.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.isThetaAdapted_iff_forall_exists_thetaPt_act_eq
    {g N n : ℕ} (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    {S : Type} [CommRing S] (ζ : S) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (X : FramedPolarisedAbelianScheme g N n S)
    (σ' : ((i : Fin g) → ZMod (δ i)) →
      Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol, ⊤))
    (hσ' : ∀ i : Fin (N + 1),
      σ' (e i) =
        (Scheme.Modules.pullbackLocalSection (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) (X.frame.σ i) :
          Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol,
            (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) ⁻¹ᵁ ⊤))) :
    X.IsThetaAdapted δ e ↔
      (∀ h : (i : Fin g) → ZMod (δ i), ∃ θ : ThetaPt X.f X.L X.pol (𝟙 (Spec (CommRingCat.of S))),
        ∀ h' : (i : Fin g) → ZMod (δ i), θ.act (σ' h') = σ' (h + h')) ∧
      (∀ c : ((i : Fin g) → ZMod (δ i)) →+ ZMod (N + 1), ∃ η : ThetaPt X.f X.L X.pol (𝟙 (Spec (CommRingCat.of S))),
        ∀ h : (i : Fin g) → ZMod (δ i), η.act (σ' h) = Polarisation.baseScalar X.f (𝟙 (Spec (CommRingCat.of S))) (ζ ^ (c h).val) • σ' h) := by sorry
