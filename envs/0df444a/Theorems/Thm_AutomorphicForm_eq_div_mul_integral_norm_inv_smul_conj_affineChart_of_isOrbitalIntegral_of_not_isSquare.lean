-- Prove2me | Theorems.Thm_AutomorphicForm_eq_div_mul_integral_norm_inv_smul_conj_affineChart_of_isOrbitalIntegral_of_not_isSquare
-- name    : AutomorphicForm.eq_div_mul_integral_norm_inv_smul_conj_affineChart_of_isOrbitalIntegral_of_not_isSquare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/aa75ea38-8347-5022-a9db-9fddd284a204
-- title:
--   Elliptic orbital integral on GL₂(Kᵥ) in an affine chart
-- statement:
--   Let $K$ be a number field, $v$ a nonzero prime of $\mathcal O_K$, and let the completion $K_v$ carry its Borel $\sigma$-algebra and an additive Haar measure $\mu$. Let $c_G$ be a nonzero finite element of $[0,\infty]$ which expresses the Haar measure [`AutomorphicForm.localHaar K v`](def/AutomorphicForm_LocalOrbitalBase.html#L168) on $\mathrm{GL}_2(K_v)$ (the Haar measure attached to the positive compact set [`AutomorphicForm.localIntegralCompacts K v`](def/AutomorphicForm_LocalOrbitalBase.html#L120)) in matrix coordinates: for every Borel measurable $H:\mathrm{GL}_2(K_v)\to[0,\infty]$, $\int H\,d(\text{localHaar})=c_G\int_{(K_v)^4}H\bigl(\begin{smallmatrix}x_0&x_1\\x_2&x_3\end{smallmatrix}\bigr)\,\|\det\|^{-2}\,d\mu^{\otimes 4}$, the integrand being read as $0$ where the determinant vanishes. Let $d\in K_v$ be a non-square, $r_0\neq 0$, $p_0\in K_v$, and let $u\in\mathrm{GL}_2(K_v)$ have matrix $\bigl(\begin{smallmatrix}p_0&r_0\\ d r_0&p_0\end{smallmatrix}\bigr)$. Let $\tau$ be a Haar measure on the centraliser [`AutomorphicForm.localCentralizer K v u`](def/AutomorphicForm_LocalOrbitalBase.html#L193) of $\{u\}$, equipped with its Borel $\sigma$-algebra, and let $c_T$ be nonzero and finite with $\int H(t)\,d\tau = c_T\int_{K_v\times K_v}H\bigl(\begin{smallmatrix}q_1&q_2\\ dq_2&q_1\end{smallmatrix}\bigr)\,\|q_1^2-dq_2^2\|^{-1}\,d(\mu\otimes\mu)$ for every Borel measurable $H\ge 0$, again with $0$ where the determinant vanishes. Let $f:\mathrm{GL}_2(K_v)\to\mathbb C$ be Borel measurable, compactly supported and bounded, and let $I\in\mathbb C$ satisfy [`AutomorphicForm.IsOrbitalIntegral K v u τ f I`](def/AutomorphicForm_LocalOrbitalBase.html#L208), i.e. there is a nonnegative, Borel measurable, compactly supported $w:\mathrm{GL}_2(K_v)\to\mathbb R$ with $\int_{T} w(tx)\,d\tau=1$ for every $x$ with $f(x^{-1}ux)\neq 0$, and $I=\int f(x^{-1}ux)\,w(x)\,d(\text{localHaar})$. Writing $\sigma(q_1,q_2)=\bigl(\begin{smallmatrix}1&0\\ q_1&q_2\end{smallmatrix}\bigr)$, the conclusion is twofold: the function $(q_1,q_2)\mapsto \|q_2\|^{-1}\,f(\sigma(q_1,q_2)^{-1}u\,\sigma(q_1,q_2))$, set to $0$ where $q_2=0$, is $\mu\otimes\mu$-integrable, and $I=(c_G/c_T)^{\mathrm{toReal}}\cdot\int \|q_2\|^{-1}f(\sigma(q_1,q_2)^{-1}u\,\sigma(q_1,q_2))\,d(\mu\otimes\mu)$.
--
--   This computes the local orbital integral of a bounded compactly supported Borel function at the regular element $u$ of the elliptic torus $K_v[\bigl(\begin{smallmatrix}0&1\\ d&0\end{smallmatrix}\bigr)]^\times$ in Langlands' coordinates $\sigma(a,b)=\bigl(\begin{smallmatrix}1&0\\ a&b\end{smallmatrix}\bigr)$ for $T\backslash\mathrm{GL}_2(K_v)$, the quotient measure appearing as $(c_G/c_T)\,da\,db/\|b\|$; in particular every value $I$ admitted by the orbital-integral predicate is given by this explicit integral, independently of the auxiliary section function $w$. It feeds the local continuity statement [`AutomorphicForm.exists_forall_nhds_scalar_forall_isOrbitalIntegral_eq_add_mul_of_mem_localCentralizer_of_not_isSquare`](thm.html#AutomorphicForm.exists_forall_nhds_scalar_forall_isOrbitalIntegral_eq_add_mul_of_mem_localCentralizer_of_not_isSquare), and the change of variables used is [`NumberField.AdicCompletion.lintegral_comp_torusAffineChart_mul_eq_lintegral`](thm.html#NumberField.AdicCompletion.lintegral_comp_torusAffineChart_mul_eq_lintegral).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_eq_div_mul_integral_norm_inv_smul_conj_affineChart_of_isOrbitalIntegral_of_not_isSquare.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

theorem AutomorphicForm.eq_div_mul_integral_norm_inv_smul_conj_affineChart_of_isOrbitalIntegral_of_not_isSquare
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (cG : ENNReal) (hcG : cG ≠ 0) (hcG' : cG ≠ ⊤)
    (hG : ∀ H : GL (Fin 2) (v.adicCompletion K) → ENNReal,
        Measurable[AutomorphicForm.localGLBorel K v] H →
        (letI := AutomorphicForm.localGLBorel K v
         ∫⁻ g, H g ∂(AutomorphicForm.localHaar K v)) =
          cG * ∫⁻ x : Fin 4 → v.adicCompletion K,
            (if h : (!![x 0, x 1; x 2, x 3] : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det ≠ 0 then
                H (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0) *
              ENNReal.ofReal
                ((‖(!![x 0, x 1; x 2, x 3] : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ ^ 2)⁻¹)
            ∂(Measure.pi fun _ : Fin 4 => μ))
    (d : v.adicCompletion K) (hd : ¬ IsSquare d) (p₀ r₀ : v.adicCompletion K) (hr₀ : r₀ ≠ 0)
    (u : GL (Fin 2) (v.adicCompletion K))
    (hu : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![p₀, r₀; d * r₀, p₀])
    (τ : @Measure (AutomorphicForm.localCentralizer K v u) (AutomorphicForm.localCentralizerBorel K v u))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v u) τ)
    (cT : ENNReal) (hcT : cT ≠ 0) (hcT' : cT ≠ ⊤)
    (hT : ∀ H : GL (Fin 2) (v.adicCompletion K) → ENNReal,
        Measurable[AutomorphicForm.localGLBorel K v] H →
        (letI := AutomorphicForm.localCentralizerBorel K v u
         ∫⁻ t, H (t : GL (Fin 2) (v.adicCompletion K)) ∂τ) =
          cT * ∫⁻ q : v.adicCompletion K × v.adicCompletion K,
            (if h : (!![q.1, q.2; d * q.2, q.1] : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det ≠ 0 then
                H (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0) *
              ENNReal.ofReal ‖q.1 ^ 2 - d * q.2 ^ 2‖⁻¹ ∂(μ.prod μ))
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfm : Measurable[AutomorphicForm.localGLBorel K v] f)
    (hfs : HasCompactSupport f) (hfb : ∃ C : ℝ, ∀ g, ‖f g‖ ≤ C)
    (I : ℂ) (hI : AutomorphicForm.IsOrbitalIntegral K v u τ f I) :
    Integrable (fun q : v.adicCompletion K × v.adicCompletion K =>
        ‖q.2‖⁻¹ • (if h : (!![1, 0; q.1, q.2] : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det ≠ 0 then
          f ((Matrix.GeneralLinearGroup.mkOfDetNeZero _ h)⁻¹ * u *
            Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0)) (μ.prod μ) ∧
      I = ((cG / cT).toReal : ℂ) *
        ∫ q : v.adicCompletion K × v.adicCompletion K,
          ‖q.2‖⁻¹ • (if h : (!![1, 0; q.1, q.2] : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det ≠ 0 then
            f ((Matrix.GeneralLinearGroup.mkOfDetNeZero _ h)⁻¹ * u *
              Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0) ∂(μ.prod μ) := by sorry
