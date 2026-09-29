-- Prove2me | Theorems.Thm_AutomorphicForm_rate_eq_mul_rate_mul_measure_pow_three_of_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_of_forall_isFundamentalDomain_op_inter_ideleNorm_det_Icc
-- name    : AutomorphicForm.rate_eq_mul_rate_mul_measure_pow_three_of_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_of_forall_isFundamentalDomain_op_inter_ideleNorm_det_Icc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/afb58e01-0e55-5280-b354-d724791f34c8
-- title:
--   Weil: GL₂ slab rate versus idelic rate and covolume
-- statement:
--   Let $K$ be a number field, with the adele ring $\mathbb A=\mathbb A_K$ and the idele group $\mathbb A^\times$ carrying their Borel structures, and equip $\mathrm{GL}_2(\mathbb A)$ with its Borel structure. Let $\tau$ be a Haar measure on $\mathrm{GL}_2(\mathbb A)$ that is in addition right invariant, $\mu$ an additive Haar measure on $\mathbb A$, and $\nu$ a Haar measure on $\mathbb A^\times$; write $\lVert x\rVert$ for the idelic norm, the value at $x$ of the distributive Haar character of the scaling action of $x$ on $\mathbb A$, and $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$. Assume: (i) $\kappa\neq\infty$ satisfies the fibration identity $\int w(g)\,\Psi(ge_1,\det g)\,d\tau=\kappa\int_{\mathbb A^2}\int_{\mathbb A^\times}\Psi(c,\delta)\lVert\delta\rVert^{-1}d\nu\,d\mu^{\otimes 2}$ for all measurable $w,\Psi$ with values in $[0,\infty]$ such that $\int w(g\,n(x))\,d\mu(x)=1$ for $\tau$-almost all $g$, where $ge_1$ is the first column of $g$; (ii) $C\neq\infty$ is such that every fundamental domain $D$ for the right-multiplication action of the image of $\mathrm{GL}_2(K)\to\mathrm{GL}_2(\mathbb A)$ satisfies $\tau(D\cap\{\lVert\det t\rVert\in[a,b]\})=C\log(b/a)$ for $0<a\le b$, and a measurable such $D_0$ exists; (iii) $C_I\neq\infty$ plays the same role for the action of the principal ideles on $\mathbb A^\times$, with a measurable fundamental domain $\Omega_0$; (iv) $B$ is a measurable additive fundamental domain for $K\subset\mathbb A$ with respect to $\mu$. Then $C=\kappa\,C_I\,\mu(B)^3$.
--
--   This is Weil's comparison of the covolume of $\mathrm{GL}_2(K)$ in $\mathrm{GL}_2(\mathbb A_K)$ with that of $K^\times$ in $\mathbb A_K^\times$, stated so as to be independent of normalisations: the growth rate $C$ of the volume of a fundamental domain over a slab $a\le\lVert\det\rVert\le b$ is the idelic rate $C_I$ times the unipotent-fibre constant $\kappa$ and the cube of the covolume of $K$ in $\mathbb A_K$. It feeds the evaluation of $C$ in terms of the discriminant and the residue of the Dedekind zeta function at $s=1$ together with $\zeta_K(2)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_rate_eq_mul_rate_mul_measure_pow_three_of_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_of_forall_isFundamentalDomain_op_inter_ideleNorm_det_Icc.lean

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

theorem AutomorphicForm.rate_eq_mul_rate_mul_measure_pow_three_of_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_of_forall_isFundamentalDomain_op_inter_ideleNorm_det_Icc
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (τ : Measure (GL (Fin 2) (AdeleRing (𝓞 K) K))) (hτ : τ.IsHaarMeasure) (hτr : τ.IsMulRightInvariant)
    (μ : Measure (AdeleRing (𝓞 K) K)) (hμ : μ.IsAddHaarMeasure)
    (ν : Measure (AdeleRing (𝓞 K) K)ˣ) (hν : ν.IsHaarMeasure)

    (κ : ENNReal) (hκ : κ ≠ ⊤)
    (hfib : ∀ (w : GL (Fin 2) (AdeleRing (𝓞 K) K) → ENNReal)
        (Ψ : (Fin 2 → AdeleRing (𝓞 K) K) × (AdeleRing (𝓞 K) K)ˣ → ENNReal),
        Measurable w → Measurable Ψ →
        (∀ᵐ g ∂τ, ∫⁻ x, w (g * AutomorphicForm.unipotentGL2 x) ∂μ = 1) →
        ∫⁻ g, w g * Ψ (fun i => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i 0,
            Matrix.GeneralLinearGroup.det g) ∂τ =
          κ * ∫⁻ c, ∫⁻ δ, Ψ (c, δ) * ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ ∂ν
            ∂(Measure.pi fun _ : Fin 2 => μ))

    (C : ENNReal) (hC : C ≠ ⊤)
    (hrate : ∀ D : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)),
      IsFundamentalDomain ((AutomorphicForm.globalPoints (𝓞 K) K).range).op D τ →
      ∀ a b : ℝ, 0 < a → a ≤ b →
        τ (D ∩ {t | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det t) ∈ Set.Icc a b}) =
          C * ENNReal.ofReal (Real.log (b / a)))
    (D₀ : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) (hD₀m : MeasurableSet D₀)
    (hD₀ : IsFundamentalDomain ((AutomorphicForm.globalPoints (𝓞 K) K).range).op D₀ τ)

    (CI : ENNReal) (hCI : CI ≠ ⊤)
    (hrateI : ∀ Ω : Set (AdeleRing (𝓞 K) K)ˣ,
      IsFundamentalDomain
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range Ω ν →
      ∀ a b : ℝ, 0 < a → a ≤ b →
        ν (Ω ∩ {x | NumberField.TateGlobal.ideleNorm K x ∈ Set.Icc a b}) =
          CI * ENNReal.ofReal (Real.log (b / a)))
    (Ω₀ : Set (AdeleRing (𝓞 K) K)ˣ) (hΩ₀m : MeasurableSet Ω₀)
    (hΩ₀ : IsFundamentalDomain
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range Ω₀ ν)

    (B : Set (AdeleRing (𝓞 K) K)) (hBm : MeasurableSet B)
    (hB : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 K) K) B μ) :
    C = κ * CI * μ B ^ 3 := by sorry
