-- Prove2me | Theorems.Thm_AlgebraicGeometry_differentiableOn_appLE_pullback_pair_of_relChart
-- name    : AlgebraicGeometry.differentiableOn_appLE_pullback_pair_of_relChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/128f493b-b003-504a-81c4-15387a3e642a
-- title:
--   Joint holomorphy of sections along the fibre square of a relative chart
-- statement:
--   Let $S_c$ be a domain which is a finite-type smooth $\mathbb{C}$-algebra whose module of Kähler differentials over $\mathbb{C}$ has rank $1$ over $S_c$, let $t \in S_c$, let $\sigma_0 : S_c \to \mathbb{C}$ be a $\mathbb{C}$-algebra map, let $r > 0$ and let $\mathcal{U}$ be a set of $\mathbb{C}$-points of $S_c$ containing $\sigma_0$ such that $\sigma \mapsto \sigma(t)$ is a bijection of $\mathcal{U}$ onto the ball $B(\sigma_0(t), r)$ and such that for each $s \in S_c$ there is a function $F$ holomorphic on $B(\sigma_0(t), r)$ with $\sigma(s) = F(\sigma(t))$ for all $\sigma \in \mathcal{U}$. Let $f : G \to \operatorname{Spec} S_c$ be a morphism of schemes, $g \in \mathbb{N}$, $\sigma_1 \in \mathcal{U}$, and $\varepsilon, \rho' > 0$ with $B(\sigma_1(t), \varepsilon) \subseteq B(\sigma_0(t), r)$, let $v_0 \in \mathbb{C}^g$, and let $\psi$ assign to each $\mathbb{C}$-point $\sigma$ of $S_c$ and each $v \in \mathbb{C}^g$ a $\mathbb{C}$-point $\psi_\sigma v$ of $G$, subject to: (i) for $\sigma \in \mathcal{U}$ with $\sigma(t) \in B(\sigma_1(t), \varepsilon)$ and $v \in B(v_0, \rho')$, $\psi_\sigma v$ followed by $f$ is $\operatorname{Spec}$ of $\sigma$; (ii) for every open $V \subseteq G$ and every $\varphi \in \Gamma(G, V)$, the set of $(z, v) \in \mathbb{C} \times \mathbb{C}^g$ with $z \in B(\sigma_1(t), \varepsilon)$, $v \in B(v_0, \rho')$ and $\sigma(t) = z$ for some $\sigma \in \mathcal{U}$ whose point $\psi_\sigma v$ factors through $V$ (that is, $\top \le (\psi_\sigma v)^{-1} V$) is open, and there is $F : \mathbb{C} \times \mathbb{C}^g \to \mathbb{C}$ differentiable on that set with $F(\sigma(t), v)$ equal to the value of $\varphi$ at $\psi_\sigma v$, computed as the image under $(\psi_\sigma v)$'s restriction map $\Gamma(G,V) \to \Gamma(\operatorname{Spec}\mathbb{C}, \top)$ and the isomorphism $\Gamma(\operatorname{Spec}\mathbb{C}, \top) \cong \mathbb{C}$. Let finally $\mathrm{pair}$ assign to $\sigma, v, w$ a $\mathbb{C}$-point of $G \times_{\operatorname{Spec} S_c} G$ whose two projections are $\psi_\sigma v$ and $\psi_\sigma w$ whenever $\sigma \in \mathcal{U}$, $\sigma(t) \in B(\sigma_1(t), \varepsilon)$ and $v, w \in B(v_0, \rho')$. Then for every open $V'$ of the fibre product and every $\varphi' \in \Gamma(G \times_{\operatorname{Spec} S_c} G, V')$, the set of $(z, (v,w))$ with $z \in B(\sigma_1(t), \varepsilon)$, $v, w \in B(v_0, \rho')$ and $\sigma(t) = z$ for some $\sigma \in \mathcal{U}$ with $\mathrm{pair}_\sigma(v,w)$ factoring through $V'$ is open, and there is $F : \mathbb{C} \times (\mathbb{C}^g \times \mathbb{C}^g) \to \mathbb{C}$ differentiable on that set with $F(\sigma(t), (v,w))$ the value of $\varphi'$ at $\mathrm{pair}_\sigma(v,w)$.
--
--   This transports the joint-holomorphy property of a relative chart on a family $G$ over an analytic chart of the base from $G$ itself to its fibre square $G \times_{\operatorname{Spec} S_c} G$, the scheme on which a relative group law is a morphism; the proof combines the affine-open analyticity criterion [`AlgebraicGeometry.IsAffineOpen.isOpen_and_exists_differentiableOn_appLE_of_forall_section`](thm.html#AlgebraicGeometry.IsAffineOpen.isOpen_and_exists_differentiableOn_appLE_of_forall_section) with the identification of sections over a product of affine opens in a fibre product as a tensor product. It is used in the construction of a relative chart at the identity on which multiplication is holomorphic, [`GoodReductionJacobian.RelativeGroupLaw.exists_relChart_one_differentiableOn_mul_of_analyticChart`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_relChart_one_differentiableOn_mul_of_analyticChart).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_differentiableOn_appLE_pullback_pair_of_relChart.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian Topology

theorem AlgebraicGeometry.differentiableOn_appLE_pullback_pair_of_relChart
    (Sc : Type) [CommRing Sc] [IsDomain Sc] [Algebra ℂ Sc] [Algebra.FiniteType ℂ Sc]
    (hSc : Algebra.Smooth ℂ Sc) (hΩ : Module.rank Sc (KaehlerDifferential ℂ Sc) = 1)
    (t : Sc) (σ₀ : Sc →ₐ[ℂ] ℂ) (r : ℝ) (𝒰 : Set (Sc →ₐ[ℂ] ℂ)) (hr : 0 < r) (hσ₀ : σ₀ ∈ 𝒰)
    (hbij : Set.BijOn (fun σ : Sc →ₐ[ℂ] ℂ => σ t) 𝒰 (Metric.ball (σ₀ t) r))
    (hhol : ∀ s : Sc, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball (σ₀ t) r) ∧ ∀ σ ∈ 𝒰, σ s = F (σ t))

    {G : Scheme.{0}} (f : G ⟶ Spec (CommRingCat.of Sc)) {g : ℕ}
    (σ₁ : Sc →ₐ[ℂ] ℂ) (hσ₁ : σ₁ ∈ 𝒰) (ε ρ' : ℝ) (hε : 0 < ε) (hρ' : 0 < ρ')
    (hεr : Metric.ball (σ₁ t) ε ⊆ Metric.ball (σ₀ t) r) (v₀ : Fin g → ℂ)
    (ψ : (Sc →ₐ[ℂ] ℂ) → (Fin g → ℂ) → (Spec (CommRingCat.of ℂ) ⟶ G))
    (hover : ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε → ∀ v ∈ Metric.ball v₀ ρ',
      ψ σ v ≫ f = Spec.map (CommRingCat.ofHom σ.toRingHom))
    (hAN : ∀ (V : G.Opens) (φ : Γ(G, V)),
      IsOpen {p : ℂ × (Fin g → ℂ) | p.1 ∈ Metric.ball (σ₁ t) ε ∧ p.2 ∈ Metric.ball v₀ ρ' ∧
        ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (ψ σ p.2) ⁻¹ᵁ V} ∧
      ∃ F : ℂ × (Fin g → ℂ) → ℂ,
        DifferentiableOn ℂ F {p : ℂ × (Fin g → ℂ) | p.1 ∈ Metric.ball (σ₁ t) ε ∧ p.2 ∈ Metric.ball v₀ ρ' ∧
          ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (ψ σ p.2) ⁻¹ᵁ V} ∧
        ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε → ∀ v ∈ Metric.ball v₀ ρ', ∀ (hV : ⊤ ≤ (ψ σ v) ⁻¹ᵁ V),
          F (σ t, v) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((ψ σ v).appLE V ⊤ hV) φ))

    (pair : (Sc →ₐ[ℂ] ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → (Spec (CommRingCat.of ℂ) ⟶ pullback f f))
    (hpair₁ : ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε → ∀ v ∈ Metric.ball v₀ ρ', ∀ w ∈ Metric.ball v₀ ρ',
      pair σ v w ≫ pullback.fst f f = ψ σ v)
    (hpair₂ : ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε → ∀ v ∈ Metric.ball v₀ ρ', ∀ w ∈ Metric.ball v₀ ρ',
      pair σ v w ≫ pullback.snd f f = ψ σ w)
    (V' : (pullback f f).Opens) (φ' : Γ(pullback f f, V')) :
    IsOpen {p : ℂ × ((Fin g → ℂ) × (Fin g → ℂ)) | p.1 ∈ Metric.ball (σ₁ t) ε ∧ p.2.1 ∈ Metric.ball v₀ ρ' ∧
        p.2.2 ∈ Metric.ball v₀ ρ' ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (pair σ p.2.1 p.2.2) ⁻¹ᵁ V'} ∧
      ∃ F : ℂ × ((Fin g → ℂ) × (Fin g → ℂ)) → ℂ,
        DifferentiableOn ℂ F {p : ℂ × ((Fin g → ℂ) × (Fin g → ℂ)) | p.1 ∈ Metric.ball (σ₁ t) ε ∧ p.2.1 ∈ Metric.ball v₀ ρ' ∧
          p.2.2 ∈ Metric.ball v₀ ρ' ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (pair σ p.2.1 p.2.2) ⁻¹ᵁ V'} ∧
        ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε → ∀ v ∈ Metric.ball v₀ ρ', ∀ w ∈ Metric.ball v₀ ρ',
          ∀ (hV : ⊤ ≤ (pair σ v w) ⁻¹ᵁ V'),
            F (σ t, (v, w)) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((pair σ v w).appLE V' ⊤ hV) φ') := by sorry
