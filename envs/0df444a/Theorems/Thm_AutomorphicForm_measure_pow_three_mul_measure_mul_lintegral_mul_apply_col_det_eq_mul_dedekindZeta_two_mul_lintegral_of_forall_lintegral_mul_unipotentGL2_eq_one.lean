-- Prove2me | Theorems.Thm_AutomorphicForm_measure_pow_three_mul_measure_mul_lintegral_mul_apply_col_det_eq_mul_dedekindZeta_two_mul_lintegral_of_forall_lintegral_mul_unipotentGL2_eq_one
-- name    : AutomorphicForm.measure_pow_three_mul_measure_mul_lintegral_mul_apply_col_det_eq_mul_dedekindZeta_two_mul_lintegral_of_forall_lintegral_mul_unipotentGL2_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/a8127870-a0b0-5955-b157-95f611722a93
-- title:
--   Unipotent integration formula for GL₂(A_K)
-- statement:
--   Let $K$ be a number field, with the adele ring $\mathbb{A}_K$ and its unit group carrying Borel $\sigma$-algebras. Fix a Haar measure $\tau_a$ on $\mathrm{GL}_2(K_\infty)$ and Haar measures $\tau_v$ on $\mathrm{GL}_2(K_v)$ for every finite place $v$ (all for the Borel structures [`AutomorphicForm.glBorelOf`](def/AutomorphicForm_TwistedOrbital.html#L57) and [`AutomorphicForm.localGLBorel`](def/AutomorphicForm_LocalOrbitalBase.html#L154)). Let $n\in\mathbb{N}$, $e:\mathrm{Fin}\,n\to M_2(K_\infty)$ and $s\in[0,\infty]$ be such that, for the $\mathbb{R}$-algebra structure on $K_\infty$ coming from the isomorphism with the mixed space, $e$ is $\mathbb{R}$-linearly independent, spans $M_2(K_\infty)$, and the image of $\tau_a$ under $\mathrm{GL}_2(K_\infty)\hookrightarrow M_2(K_\infty)$ equals $s$ times the measure obtained from Lebesgue measure transported along $c\mapsto\sum_i c_ie_i$, scaled by $\sqrt{|\det(\mathrm{Tr}_{K_\infty/\mathbb{R}}\mathrm{tr}(e_ie_j))_{i,j}|}$ and given density $|N_{K_\infty/\mathbb{R}}(\det X)|^{-2}$. Let $S_0$ be a finite set of finite places, $\tau$ a Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$ and $c_\tau>0$ a real number such that $\tau$ factorises as a restricted product with constant $c_\tau$: for every finite $S\supseteq S_0$ and all $\mathbb{C}$-valued $W$, $W_\infty$, $W_v$ with $W_\infty$ and the $W_v$ ($v\in S$) a.e. strongly measurable, if $W(t)=W_\infty(t_\infty)\prod_{v\in S}W_v(t_v)$ whenever every component $t_v$ off $S$ lies in [`AutomorphicForm.localIntegralSet`](def/AutomorphicForm_LocalOrbitalBase.html#L100) (i.e. $t_v$ and $t_v^{-1}$ have entries in $\mathcal{O}_v$), and $W(t)=0$ whenever some component off $S$ fails this, then $\int W\,d\tau=c_\tau\bigl(\int W_\infty\,d\tau_a\bigr)\prod_{v\in S}\int W_v\,d\tau_v$. Let $\mu$ be an additive Haar measure on $\mathbb{A}_K$ and $\nu$ a Haar measure on $\mathbb{A}_K^\times$. Then $s\neq\infty$, and for all measurable $w:\mathrm{GL}_2(\mathbb{A}_K)\to[0,\infty]$ and $\Psi:(\mathrm{Fin}\,2\to\mathbb{A}_K)\times\mathbb{A}_K^\times\to[0,\infty]$ satisfying $\int^-w\bigl(g\,\binom{1\ x}{0\ 1}\bigr)\,d\mu(x)=1$ for $\tau$-almost every $g$, one has $$\mu(E)^3\,\nu(\mathrm{Sh})\int^- w(g)\,\Psi\bigl(ge_1,\det g\bigr)\,d\tau(g)=c_\tau\,s\Bigl(\prod_{v\in S_0}\tau_v(\text{integral set at }v)\Bigr)\,2^{4r_2+r_1}(2\pi)^{r_2}\,\mathrm{Re}\,\zeta_K(2)\int^-\!\!\int^-\Psi(c,\delta)\,\|\delta\|^{-1}\,d\nu(\delta)\,d\mu^{\otimes 2}(c),$$ where $ge_1$ denotes the first column of $g$, $\|\delta\|$ is the idele norm (the value of the distributive Haar character of $\mathbb{A}_K$ at $\delta$), $E$ is the set of adeles whose archimedean component has all real coordinates and all real and imaginary parts of complex coordinates in $[0,1]$ and whose finite component is everywhere integral, and $\mathrm{Sh}$ is the set of ideles $u$ with $u_v,(u^{-1})_v\in\mathcal{O}_v$ at all finite $v$ and $\|u_w\|\in[1,e]$ at all infinite places $w$.
--
--   This is Weil's integration formula $\int_G=\int_{G/N}\int_N$ for $G=\mathrm{GL}_2(\mathbb{A}_K)$ and the unipotent radical $N=\{\binom{1\ x}{0\ 1}\}$ of the stabiliser of the first basis vector, the quotient being identified with the pairs (first column, determinant) and carrying the invariant measure $\|\delta\|^{-1}\,d\nu(\delta)\,d\mu^{\otimes 2}(c)$, with the constant made explicit for the stated normalisations of $\tau$, $\tau_a$ and the $\tau_v$. It supplies the constant of integration along unipotent fibres in the computation of the covolume of $\mathrm{GL}_2(K)$ in $\mathrm{GL}_2(\mathbb{A}_K)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_measure_pow_three_mul_measure_mul_lintegral_mul_apply_col_det_eq_mul_dedekindZeta_two_mul_lintegral_of_forall_lintegral_mul_unipotentGL2_eq_one.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.measure_pow_three_mul_measure_mul_lintegral_mul_apply_col_det_eq_mul_dedekindZeta_two_mul_lintegral_of_forall_lintegral_mul_unipotentGL2_eq_one
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]

    (τa : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (hτa : @Measure.IsHaarMeasure (GL (Fin 2) (InfiniteAdeleRing K)) _ _
      (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) τa)
    (τf : ∀ v : HeightOneSpectrum (𝓞 K),
      @Measure (GL (Fin 2) (v.adicCompletion K)) (AutomorphicForm.localGLBorel K v))
    (hτf : ∀ v, @Measure.IsHaarMeasure (GL (Fin 2) (v.adicCompletion K)) _ _
      (AutomorphicForm.localGLBorel K v) (τf v))

    (n : ℕ) (e : Fin n → Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) (s : ENNReal)
    (harch :
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) := borel _
      letI := AutomorphicForm.glBorelOf (InfiniteAdeleRing K)
      LinearIndependent ℝ e ∧
        Submodule.span ℝ (Set.range e) = ⊤ ∧
        Measure.map (fun t : GL (Fin 2) (InfiniteAdeleRing K) =>
            (t : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))) τa =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n =>
                  Algebra.trace ℝ (InfiniteAdeleRing K) (Matrix.trace (e i * e j))).det|)) •
                Measure.map (fun c : Fin n → ℝ => ∑ i, c i • e i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)| ^ 2)⁻¹))

    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (τ : Measure (GL (Fin 2) (AdeleRing (𝓞 K) K))) (hτ : τ.IsHaarMeasure) (cτ : ℝ) (hcτ : 0 < cτ)
    (hτprod : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), S₀ ⊆ S →
        ∀ (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] Wa τa →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localGLBorel K v] (WS v) (τf v)) →
        (∀ t : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∈
              AutomorphicForm.localIntegralSet K v) →
            W t = Wa (AdelicLevel.glArch (𝓞 K) K t) *
              ∏ v ∈ S, WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t))) →
        (∀ t : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∉
              AutomorphicForm.localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂τ = cτ * (∫ x, Wa x ∂τa) * ∏ v ∈ S, ∫ y, WS v y ∂(τf v))

    (μ : Measure (AdeleRing (𝓞 K) K)) (hμ : μ.IsAddHaarMeasure)
    (ν : Measure (AdeleRing (𝓞 K) K)ˣ) (hν : ν.IsHaarMeasure) :
    s ≠ ⊤ ∧
    ∀ (w : GL (Fin 2) (AdeleRing (𝓞 K) K) → ENNReal)
      (Ψ : (Fin 2 → AdeleRing (𝓞 K) K) × (AdeleRing (𝓞 K) K)ˣ → ENNReal),
      Measurable w → Measurable Ψ →
      (∀ᵐ g ∂τ, ∫⁻ x, w (g * AutomorphicForm.unipotentGL2 x) ∂μ = 1) →
      μ {x | ((∀ w : {w : InfinitePlace K // w.IsReal},
              (InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).1 w ∈ Set.Icc (0 : ℝ) 1) ∧
            ∀ w : {w : InfinitePlace K // w.IsComplex},
              ((InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).2 w).re ∈ Set.Icc (0 : ℝ) 1 ∧
              ((InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).2 w).im ∈ Set.Icc (0 : ℝ) 1) ∧
          x.2 ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 K) K} ^ 3 *
        ν {u | (∀ v : HeightOneSpectrum (𝓞 K),
            ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
            (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈
              v.adicCompletionIntegers K) ∧
          ∀ w : InfinitePlace K, ‖(u : AdeleRing (𝓞 K) K).1 w‖ ∈ Set.Icc (1 : ℝ) (Real.exp 1)} *
        ∫⁻ g, w g * Ψ (fun i => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i 0,
            Matrix.GeneralLinearGroup.det g) ∂τ =
      ENNReal.ofReal cτ * s * (∏ v ∈ S₀, τf v (AutomorphicForm.localIntegralSet K v)) *
        (2 ^ (4 * NumberField.InfinitePlace.nrComplexPlaces K + NumberField.InfinitePlace.nrRealPlaces K) *
          ENNReal.ofReal ((2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K) *
          ENNReal.ofReal (NumberField.dedekindZeta K 2).re) *
        ∫⁻ c, ∫⁻ δ, Ψ (c, δ) * ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ ∂ν
          ∂(Measure.pi fun _ : Fin 2 => μ) := by sorry
