-- Prove2me | Theorems.Thm_AutomorphicForm_tsum_sigmaCentralizer_apply_mulVec_add_eq_inv_ideleNorm_det_mul_tsum_reflectPair_of_forall_ne_scalar_of_finrank_eq_two
-- name    : AutomorphicForm.tsum_sigmaCentralizer_apply_mulVec_add_eq_inv_ideleNorm_det_mul_tsum_reflectPair_of_forall_ne_scalar_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/9dec9b2d-0409-5972-a276-5c1ae6dc87c4
-- title:
--   Poisson summation over a σ-twisted centralizer in GL₂
-- statement:
--   Let $K$ be a field of characteristic zero and $L$ a number field with a $K$-algebra structure such that $\operatorname{finrank}_K L = 2$, and let $\sigma : L \simeq_K L$ be an automorphism such that every $K$-automorphism of $L$ lies in the subgroup of integer powers of $\sigma$. Let $\delta_0 \in \mathrm{GL}_2(L)$ satisfy: $\delta_0$ times the entrywise $\sigma$-image of $\delta_0$ is a scalar matrix $z \cdot 1$ for some $z \in L^\times$, and for no $x \in \mathrm{GL}_2(L)$ and $z \in L^\times$ is $x^{-1}\delta_0\,\sigma(x)$ equal to $z \cdot 1$. Fix $v \in L^2$ with $v \neq 0$. On the adele ring $\mathbb{A}_L$ take a measurable and Borel structure, an additive Haar measure $\mu_1$ normalised so that the adelic box (points whose infinite component lies in the preimage of the fundamental domain of the lattice basis and whose finite component is integral at every finite place) has measure $1$, and an additive character $\psi : \mathbb{A}_L \to \mathbb{C}^\times$ that is continuous, non-trivial, and trivial on the image of $L$. Let $\Phi$ lie in $\mathtt{schwartzBruhat2}\ L$, the $\mathbb{C}$-span of products $x \mapsto g(x_\infty)h(x_{\mathrm{fin}})$ with $g$ Schwartz on the two-fold mixed space and $h$ locally constant with compact support on $(\mathbb{A}_{L,\mathrm{fin}})^2$, and let $g \in \mathrm{GL}_2(\mathbb{A}_L)$. Write $\Gamma$ for the subgroup $\{t \in \mathrm{GL}_2(L) \mid t\,\delta_0\,\sigma(t)^{-1} = \delta_0\}$, the $\sigma$-twisted centraliser of $\delta_0$, and $\Phi' = \mathtt{reflectPair}\,\psi\,\mu_1\,\Phi$, given by $\Phi'(x) = \widehat{\Phi}(x_1, -x_0)$ where $\widehat{\Phi}$ is the Fourier transform against the pair character built from $\psi$ and the product Haar measure built from $\mu_1$. The conclusion asserts three things: the family $\gamma \mapsto \Phi\bigl(g \cdot \iota(\gamma v)\bigr)$ is summable over $\Gamma$, where $\iota$ is the componentwise embedding $L^2 \to \mathbb{A}_L^2$ and $g$ acts on column vectors; the family $\gamma \mapsto \Phi'\bigl((\det g)^{-1} \cdot g \cdot \iota(\gamma v)\bigr)$ is summable over $\Gamma$; and $$\sum_{\gamma \in \Gamma} \Phi\bigl(g\,\iota(\gamma v)\bigr) + \Phi(0) = \lVert \det g \rVert^{-1}\Bigl(\sum_{\gamma \in \Gamma} \Phi'\bigl((\det g)^{-1} g\,\iota(\gamma v)\bigr) + \Phi'(0)\Bigr),$$ where $\lVert \cdot \rVert$ denotes the idele norm of $L$, defined through the scaling factor of Haar measure on $\mathbb{A}_L$.
--
--   This is the theta inversion (Poisson summation) formula attached to the $\sigma$-twisted centraliser of $\delta_0$, a quaternionic unit group inside $\mathrm{GL}_2(L)$, read through the bijection $\gamma \mapsto \gamma v$ onto the nonzero vectors of $L^2$, so that summation over the unit group becomes summation over $L^2 \setminus \{0\}$ and the adelic Poisson formula for $\Phi$ on $\mathbb{A}_L^2$ applies. It feeds the functional equation of the associated zeta integral, and is used in the evaluation of the corresponding integral over a fundamental domain for the twisted centraliser.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_tsum_sigmaCentralizer_apply_mulVec_add_eq_inv_ideleNorm_det_mul_tsum_reflectPair_of_forall_ne_scalar_of_finrank_eq_two.lean

import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_SigmaCentralizer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal
  AutomorphicForm

theorem AutomorphicForm.tsum_sigmaCentralizer_apply_mulVec_add_eq_inv_ideleNorm_det_mul_tsum_reflectPair_of_forall_ne_scalar_of_finrank_eq_two
    (K L : Type) [Field K] [CharZero K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L)
    (hN : ∃ z : Lˣ, δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (v : Fin 2 → L) (hv : v ≠ 0)
    [MeasurableSpace (AdeleRing (𝓞 L) L)] [BorelSpace (AdeleRing (𝓞 L) L)]
    (μ₁ : Measure (AdeleRing (𝓞 L) L)) [μ₁.IsAddHaarMeasure] (hμ₁ : μ₁ (adelicBox L) = 1)
    {ψ : AddChar (AdeleRing (𝓞 L) L) ℂ} (hψ : IsGlobalAddChar L ψ)
    {Φ : (Fin 2 → AdeleRing (𝓞 L) L) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 L)
    (g : GL (Fin 2) (AdeleRing (𝓞 L) L)) :
    Summable (fun γ : ↥(sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀) =>
      Φ ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec fun i =>
        algebraMap L (AdeleRing (𝓞 L) L)
          ((((γ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).mulVec v) i))) ∧
    Summable (fun γ : ↥(sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀) =>
      reflectPair ψ μ₁ Φ ((((Matrix.GeneralLinearGroup.det g)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) :
          AdeleRing (𝓞 L) L) •
        (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec fun i =>
          algebraMap L (AdeleRing (𝓞 L) L)
            ((((γ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).mulVec v) i))) ∧
    ∑' γ : ↥(sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀),
        Φ ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec fun i =>
          algebraMap L (AdeleRing (𝓞 L) L)
            ((((γ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).mulVec v) i))
      + Φ 0 =
    (((ideleNorm L (Matrix.GeneralLinearGroup.det g))⁻¹ : ℝ) : ℂ) *
      (∑' γ : ↥(sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀),
          reflectPair ψ μ₁ Φ ((((Matrix.GeneralLinearGroup.det g)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) :
              AdeleRing (𝓞 L) L) •
            (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec fun i =>
              algebraMap L (AdeleRing (𝓞 L) L)
                ((((γ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).mulVec v) i))
        + reflectPair ψ μ₁ Φ 0) := by sorry
