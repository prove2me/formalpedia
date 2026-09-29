-- Prove2me | Theorems.Thm_AutomorphicForm_setLIntegral_mul_tsum_apply_mulVec_eq_mul_measure_mul_lintegral_mul_setLIntegral_of_isFundamentalDomain_op
-- name    : AutomorphicForm.setLIntegral_mul_tsum_apply_mulVec_eq_mul_measure_mul_lintegral_mul_setLIntegral_of_isFundamentalDomain_op
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/be7e2ede-498e-57dd-b2a2-270ec3e4da0c
-- title:
--   Unfolding the GL₂ theta integral over a fundamental domain
-- statement:
--   Let $K$ be a number field, $\mathbb{A} = \mathbb{A}_K$ its adele ring and $\mathbb{A}^\times$ its idele group, each with its Borel $\sigma$-algebra, and let $\mathrm{GL}_2(\mathbb{A})$ carry the Borel $\sigma$-algebra. Let $\tau$ be a Haar measure on $\mathrm{GL}_2(\mathbb{A})$ that is in addition right invariant, $\mu$ an additive Haar measure on $\mathbb{A}$, $\nu$ an arbitrary measure on $\mathbb{A}^\times$, and $\kappa \in [0,\infty]$. Write $\|\delta\|$ for [`NumberField.TateGlobal.ideleNorm K δ`](def/NumberField_TateGlobalZeta.html#L19), the value at $\delta$ of the distributive Haar character of $\mathbb{A}$ viewed as a real number, and $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$ for [`AutomorphicForm.unipotentGL2 x`](def/AutomorphicForm_ConstantTerm.html#L17). The hypothesis `hfib` is a fibre-integration identity along $g \mapsto (g e_1, \det g)$: for all measurable $w \colon \mathrm{GL}_2(\mathbb{A}) \to [0,\infty]$ and $\Psi \colon \mathbb{A}^2 \times \mathbb{A}^\times \to [0,\infty]$ such that $\int_{\mathbb{A}} w(g\,n(x))\,d\mu(x) = 1$ for $\tau$-almost every $g$, one has $\int w(g)\,\Psi(g e_1, \det g)\,d\tau = \kappa \int_{\mathbb{A}^2}\int_{\mathbb{A}^\times} \Psi(c,\delta)\,\|\delta\|^{-1}\,d\nu\,d\mu^{\otimes 2}$, where $g e_1$ denotes the first column of $g$. Further data: a measurable $D \subseteq \mathrm{GL}_2(\mathbb{A})$ which is a fundamental domain for $\tau$ under the opposite of the range of [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15), i.e. for right multiplication by the image of $\mathrm{GL}_2(K)$ under the entrywise map $\mathrm{algebraMap}\,K\,\mathbb{A}$; a measurable $\Omega \subseteq \mathbb{A}^\times$ which is a fundamental domain for $\nu$ under the range of $\mathrm{algebraMap}$ on units, i.e. the principal ideles; a set $B \subseteq \mathbb{A}$ which is an additive fundamental domain for $\mu$ under `AdeleRing.principalSubgroup`, the image of $K$ in $\mathbb{A}$; and measurable $\Phi \colon \mathbb{A}^2 \to [0,\infty]$, $h \colon \mathbb{R} \to [0,\infty]$. The conclusion is the identity of $[0,\infty]$-valued integrals $$\int_{D} h(\|\det g\|) \sum_{0 \neq \xi \in K^2} \Phi(g\xi)\,d\tau(g) = \kappa\,\mu(B)\left(\int_{\mathbb{A}^2}\Phi\,d\mu^{\otimes 2}\right)\int_{\Omega} h(\|\delta\|)\,\|\delta\|^{-1}\,d\nu(\delta),$$ the sum being over the nonzero $\xi \colon \mathrm{Fin}\,2 \to K$ and $g\xi$ meaning the matrix–vector product of $g$ with the entrywise image of $\xi$ in $\mathbb{A}^2$.
--
--   This is the unfolding step in Weil's computation of the volume of $\mathrm{GL}_2(K)\backslash\mathrm{GL}_2(\mathbb{A})$ by means of the theta series $\Theta_\Phi(g) = \sum_{\xi \neq 0}\Phi(g\xi)$, the same manipulation that underlies Siegel's mean value theorem, stated here for arbitrary normalisations of $\tau$, $\mu$ and $\nu$. It feeds the subsequent comparison of volumes of fundamental domains cut out by conditions on $\|\det g\|$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setLIntegral_mul_tsum_apply_mulVec_eq_mul_measure_mul_lintegral_mul_setLIntegral_of_isFundamentalDomain_op.lean

import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.setLIntegral_mul_tsum_apply_mulVec_eq_mul_measure_mul_lintegral_mul_setLIntegral_of_isFundamentalDomain_op
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (τ : Measure (GL (Fin 2) (AdeleRing (𝓞 K) K))) (hτ : τ.IsHaarMeasure) (hτr : τ.IsMulRightInvariant)
    (μ : Measure (AdeleRing (𝓞 K) K)) (hμ : μ.IsAddHaarMeasure)
    (ν : Measure (AdeleRing (𝓞 K) K)ˣ)

    (κ : ENNReal)
    (hfib : ∀ (w : GL (Fin 2) (AdeleRing (𝓞 K) K) → ENNReal)
        (Ψ : (Fin 2 → AdeleRing (𝓞 K) K) × (AdeleRing (𝓞 K) K)ˣ → ENNReal),
        Measurable w → Measurable Ψ →
        (∀ᵐ g ∂τ, ∫⁻ x, w (g * AutomorphicForm.unipotentGL2 x) ∂μ = 1) →
        ∫⁻ g, w g * Ψ (fun i => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i 0,
            Matrix.GeneralLinearGroup.det g) ∂τ =
          κ * ∫⁻ c, ∫⁻ δ, Ψ (c, δ) * ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ ∂ν
            ∂(Measure.pi fun _ : Fin 2 => μ))

    (D : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) (hDm : MeasurableSet D)
    (hD : IsFundamentalDomain ((AutomorphicForm.globalPoints (𝓞 K) K).range).op D τ)

    (Ω : Set (AdeleRing (𝓞 K) K)ˣ) (hΩm : MeasurableSet Ω)
    (hΩ : IsFundamentalDomain
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range Ω ν)

    (B : Set (AdeleRing (𝓞 K) K))
    (hB : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 K) K) B μ)

    (Φ : (Fin 2 → AdeleRing (𝓞 K) K) → ENNReal) (hΦ : Measurable Φ)
    (h : ℝ → ENNReal) (hh : Measurable h) :
    ∫⁻ g in D, h (NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) *
        ∑' ξ : {ξ : Fin 2 → K // ξ ≠ 0},
          Φ ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).mulVec
            fun i => algebraMap K (AdeleRing (𝓞 K) K) (ξ.1 i)) ∂τ =
      κ * μ B * (∫⁻ c, Φ c ∂(Measure.pi fun _ : Fin 2 => μ)) *
        ∫⁻ δ in Ω, h (NumberField.TateGlobal.ideleNorm K δ) *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ ∂ν := by sorry
