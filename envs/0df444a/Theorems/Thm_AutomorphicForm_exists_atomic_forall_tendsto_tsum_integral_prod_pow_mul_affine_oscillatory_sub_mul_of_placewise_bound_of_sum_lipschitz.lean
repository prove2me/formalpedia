-- Prove2me | Theorems.Thm_AutomorphicForm_exists_atomic_forall_tendsto_tsum_integral_prod_pow_mul_affine_oscillatory_sub_mul_of_placewise_bound_of_sum_lipschitz
-- name    : AutomorphicForm.exists_atomic_forall_tendsto_tsum_integral_prod_pow_mul_affine_oscillatory_sub_mul_of_placewise_bound_of_sum_lipschitz
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/88eebeaf-9d2a-53d7-b815-2e30dd7fe0e6
-- title:
--   Large-R limit: slope, summable atoms, small functional
-- statement:
--   Let $K$ be a number field, $S_K$ a finite set of finite places of $K$ (height-one primes of $\mathcal O_K$), and $X$ a non-empty compact set of tables $x=(x_v)_v$ with $x_v\in\mathbb C^2$. Write $q_v$ for the absolute norm of $v$ viewed in $\mathbb C$ (this is `HeckeEigensystem.cNorm v`). Let $\iota_E$ be a countable index set with sizes $n_E(e)$, and let $A,B:\iota_E\times\{\text{places}\}\to\mathbb C$ be nowhere zero with $\|A_{e,v}\|,\|B_{e,v}\|\le M_0(v)$ for all $e$. Let $\tau_e(t)$ be tables with $\tau_e(t)_v=\bigl(q_v^{1/2}(A_{e,v}q_v^{-it}+B_{e,v}q_v^{it}),\,q_vA_{e,v}B_{e,v}\bigr)$ for $v\notin S_K$, $\tau_e(t)_v=0$ for $v\in S_K$, and $\tau_e(t)\in X$ always. Let $\kappa,c\in\mathbb C$ and, for each $e$ and $i,j<n_E(e)$, let $P_{e,ij},Q_{e,ij},U_{e,ij},V_{e,ij},a_{e,ij}:\mathbb R\to\mathbb C$ satisfy: $P_{e,ij}$ constant; $Q,U,V,a$ continuous; $a_{e,ij}$, $a_{e,ij}Q_{e,ij}$, $a_{e,ij}U_{e,ij}$, $a_{e,ij}V_{e,ij}$ integrable; $U_{e,ij}(0)=V_{e,ij}(0)$. Let $L:\iota_E\to\mathbb R$ be summable and dominate, for each $e$, the sum over $(i,j)$ of $\int(\|a\|(1+\|P\|)+\|aQ\|+\|aU\|+\|aV\|)$, the sum of $\|a_{e,ij}(0)\|(\|U_{e,ij}(0)\|+\|V_{e,ij}(0)\|)$, and, for $|t|\le1$, the two Lipschitz-type sums $\sum_{i,j}\|a(U+V)(t)-a(U+V)(0)\|\le L(e)|t|$ and $\sum_{i,j}\|a(U-V)(t)\|\le L(e)|t|$. Then there are tables $t_n\in X$ and coefficients $c_n$ with $\sum_n\|c_n\|<\infty$, each charged $t_n$ (i.e. $c_n\neq0$) being $\tau_e(0)$ for some $e$ with $n_E(e)>0$, such that for every finite set $T$ of places disjoint from $S_K$ with $\#T\ge2$ there is a continuous linear functional $\Lambda$ on $C(X,\mathbb C)$ which is small on functions concentrated near a prescribed table in the $T$-coordinates — for every table $\sigma$ and every $\varepsilon>0$ there are open sets $U_v\ni\sigma_v$ ($v\in T$) with $\|\Lambda g\|<\varepsilon$ whenever $\|g\|\le1$ and $g$ vanishes at all $y\in X$ with $y_v\notin U_v$ for some $v\in T$ — and a continuous linear functional $s$ on $C(X,\mathbb C)$ with the following property: for all exponent functions $k,j$ on places, every $g\in C(X,\mathbb C)$ given on $X$ by $g(x)=\prod_{v\in T}(x_v)_1^{k_v}\,(q_v^{-1}(x_v)_2)^{j_v}$, and every $I:\mathbb R\to\mathbb C$ and $R_0$ such that for all $R\ge R_0$
--   $$I(R)=\kappa\sum_{e}\int_{\mathbb R}\sum_{i,j}\bigl(g(\tau_e(t))a_{e,ij}(t)\bigr)c\Bigl(2RP_{e,ij}(t)-Q_{e,ij}(t)+\frac{U_{e,ij}(t)e^{2iRt}}{2it}-\frac{V_{e,ij}(t)e^{-2iRt}}{2it}\Bigr)\,dt,$$
--   one has $I(R)-R\,s(g)\to\sum_n c_n\,g(t_n)+\Lambda(g)$ as $R\to\infty$.
--
--   This is the packaging of the continuous-spectrum contribution in the Arthur–Selberg trace formula for $\mathrm{GL}_2$, isolated as a statement of real and Fourier analysis: a linear-in-$R$ term (the slope $s$), an absolutely summable atomic part supported on the tables $\tau_e(0)$, and a remainder functional $\Lambda$ that is small on test functions concentrated near a point in the coordinates from $T$. It feeds the later steps that compare the spectral and geometric sides for the Hecke tables $\tau_e$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_atomic_forall_tendsto_tsum_integral_prod_pow_mul_affine_oscillatory_sub_mul_of_placewise_bound_of_sum_lipschitz.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_atomic_forall_tendsto_tsum_integral_prod_pow_mul_affine_oscillatory_sub_mul_of_placewise_bound_of_sum_lipschitz
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (X : Set (HeightOneSpectrum (𝓞 K) → ℂ × ℂ)) (hXc : IsCompact X) (hX0 : X.Nonempty)
    (ιE : Type) [Countable ιE] (nE : ιE → ℕ)
    (A B : ιE → HeightOneSpectrum (𝓞 K) → ℂ) (hA : ∀ e v, A e v ≠ 0) (hB : ∀ e v, B e v ≠ 0)
    (M₀ : HeightOneSpectrum (𝓞 K) → ℝ) (hAM : ∀ e v, ‖A e v‖ ≤ M₀ v) (hBM : ∀ e v, ‖B e v‖ ≤ M₀ v)
    (τ : ιE → ℝ → (HeightOneSpectrum (𝓞 K) → ℂ × ℂ))
    (hτ : ∀ (e : ιE) (t : ℝ) (v : HeightOneSpectrum (𝓞 K)), v ∉ SK →
      τ e t v = ((HeckeEigensystem.cNorm v) ^ ((1 / 2 : ℝ) : ℂ) *
          (A e v * (HeckeEigensystem.cNorm v) ^ (-((t : ℂ) * Complex.I)) + B e v * (HeckeEigensystem.cNorm v) ^ ((t : ℂ) * Complex.I)),
        (HeckeEigensystem.cNorm v) * A e v * B e v))
    (hτS : ∀ (e : ιE) (t : ℝ) (v : HeightOneSpectrum (𝓞 K)), v ∈ SK → τ e t v = 0)
    (hτX : ∀ e t, τ e t ∈ X)
    (κ c : ℂ)
    (P Q U V a : ∀ e : ιE, Fin (nE e) → Fin (nE e) → ℝ → ℂ)
    (hPc : ∀ e i j t, P e i j t = P e i j 0)
    (hQc : ∀ e i j, Continuous (Q e i j)) (hUc : ∀ e i j, Continuous (U e i j)) (hVc : ∀ e i j, Continuous (V e i j))
    (hac : ∀ e i j, Continuous (a e i j)) (hai : ∀ e i j, Integrable (a e i j))
    (haQ : ∀ e i j, Integrable (fun t => a e i j t * Q e i j t))
    (haU : ∀ e i j, Integrable (fun t => a e i j t * U e i j t))
    (haV : ∀ e i j, Integrable (fun t => a e i j t * V e i j t))
    (hUV0 : ∀ e i j, U e i j 0 = V e i j 0)
    (L : ιE → ℝ) (hL : Summable L)
    (hL1 : ∀ e, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
        ∫ t : ℝ, (‖a e i j t‖ * (1 + ‖P e i j t‖) + ‖a e i j t * Q e i j t‖ +
          ‖a e i j t * U e i j t‖ + ‖a e i j t * V e i j t‖) ≤ L e)
    (hL0 : ∀ e, ∑ i : Fin (nE e), ∑ j : Fin (nE e), ‖a e i j 0‖ * (‖U e i j 0‖ + ‖V e i j 0‖) ≤ L e)
    (hLip : ∀ (e : ιE) (t : ℝ), |t| ≤ 1 →
        (∑ i : Fin (nE e), ∑ j : Fin (nE e),
          ‖a e i j t * (U e i j t + V e i j t) - a e i j 0 * (U e i j 0 + V e i j 0)‖) ≤ L e * |t| ∧
        (∑ i : Fin (nE e), ∑ j : Fin (nE e), ‖a e i j t * (U e i j t - V e i j t)‖) ≤ L e * |t|) :
    ∃ (tabs : ℕ → (HeightOneSpectrum (𝓞 K) → ℂ × ℂ)) (htabs : ∀ n, tabs n ∈ X) (cs : ℕ → ℂ),
    (Summable fun n => ‖cs n‖) ∧
    (∀ n, cs n ≠ 0 → ∃ e : ιE, 0 < nE e ∧ tabs n = τ e 0) ∧
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), Disjoint T SK → 2 ≤ T.card →
      ∃ Λ : C(X, ℂ) →L[ℂ] ℂ,
      (∀ (τ : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), ∀ ε > (0 : ℝ),
        ∃ U : HeightOneSpectrum (𝓞 K) → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
          ∀ g : C(X, ℂ),
            (∀ y : X, (∃ v ∈ T, (y : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) v ∉ U v) → g y = 0) →
            (∀ y, ‖g y‖ ≤ 1) → ‖Λ g‖ < ε) ∧
      ∃ s : C(X, ℂ) →L[ℂ] ℂ,
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ),
      ∀ g : C(X, ℂ),
        (∀ x : X, g x = ∏ v ∈ T,
          ((x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) v).1 ^ ks v *
            ((HeckeEigensystem.cNorm v)⁻¹ *
              ((x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) v).2) ^ js v) →
      ∀ (I : ℝ → ℂ) (R₀ : ℝ),
        (∀ R : ℝ, R₀ ≤ R →
          I R = κ * ∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
            (g ⟨τ e t, hτX e t⟩ * a e i j t) *
              (c * ( P e i j t * (2 * (R : ℂ))
                    - Q e i j t
                    + U e i j t * Complex.exp (2 * Complex.I * (R : ℂ) * (t : ℂ)) / (2 * Complex.I * (t : ℂ))
                    - V e i j t * Complex.exp (-(2 * Complex.I * (R : ℂ) * (t : ℂ))) / (2 * Complex.I * (t : ℂ)) ))) →
        Filter.Tendsto (fun R : ℝ => I R - (R : ℂ) * s g) Filter.atTop
          (nhds ((∑' n, cs n * g ⟨tabs n, htabs n⟩) + Λ g)) := by sorry
