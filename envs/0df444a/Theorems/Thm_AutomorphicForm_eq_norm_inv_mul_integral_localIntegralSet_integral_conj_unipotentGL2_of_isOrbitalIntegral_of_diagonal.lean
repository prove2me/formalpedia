-- Prove2me | Theorems.Thm_AutomorphicForm_eq_norm_inv_mul_integral_localIntegralSet_integral_conj_unipotentGL2_of_isOrbitalIntegral_of_diagonal
-- name    : AutomorphicForm.eq_norm_inv_mul_integral_localIntegralSet_integral_conj_unipotentGL2_of_isOrbitalIntegral_of_diagonal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/384c6896-a0c9-5a5a-a57e-d5cda10c5455
-- title:
--   Regular diagonal orbital integral descends to the unipotent radical
-- statement:
--   Let $K$ be a number field, $v$ a nonzero prime of $\mathcal O_K$, and $F = K_v$ the $v$-adic completion, with ring of integers $\mathcal O_v$ and normalised absolute value $\|\cdot\|$. Let $\gamma \in \mathrm{GL}_2(F)$ satisfy: $\operatorname{tr}(\gamma)^2 - 4\det(\gamma)$ is a unit of $F$ (the project's regular semisimplicity), and the entries $\gamma_{01}$ and $\gamma_{10}$ vanish, so $\gamma = \mathrm{diag}(\gamma_{00},\gamma_{11})$. Let $\tau$ be a Haar measure on the centraliser $T_\gamma$ of $\{\gamma\}$ in $\mathrm{GL}_2(F)$ for its Borel $\sigma$-algebra, let $\nu$ be an additive Haar measure on $F$, and let $f : \mathrm{GL}_2(F) \to \mathbb{C}$ be locally constant with compact support. Write $\mathcal K$ for the set of $g$ with both $g$ and $g^{-1}$ having all entries in $\mathcal O_v$, and $\mu$ for the Haar measure on $\mathrm{GL}_2(F)$ normalised by $\mu(\mathcal K) = 1$. Assume $I \in \mathbb{C}$ is a value of the orbital integral of $f$ at $\gamma$ relative to $\tau$: for some $w : \mathrm{GL}_2(F) \to \mathbb{R}$ that is nonnegative, Borel measurable and compactly supported and satisfies $\int_{T_\gamma} w(tx)\,d\tau(t) = 1$ whenever $f(x^{-1}\gamma x) \neq 0$, one has $I = \int f(x^{-1}\gamma x)\,w(x)\,d\mu(x)$. Then, with $n(u) = \begin{pmatrix}1&u\\0&1\end{pmatrix}$, $$I = \bigl(\tau(T_\gamma \cap \mathcal K)\,\nu(\mathcal O_v)\,\|1 - \gamma_{11}/\gamma_{00}\|\bigr)^{-1} \int_{\mathrm{GL}_2(F)} \mathbf 1_{\mathcal K}(k) \int_F f\bigl(k^{-1}\gamma\, n(u)\,k\bigr)\,d\nu(u)\,d\mu(k),$$ the real constant (formed from the real values of the two measures) being coerced into $\mathbb{C}$.
--
--   This is Harish-Chandra's descent of a split (hyperbolic) orbital integral on $\mathrm{GL}_2$ over a non-archimedean local field to the unipotent radical: the integral over $T_\gamma \backslash \mathrm{GL}_2(F)$ is expressed as $\|1-\gamma_{11}/\gamma_{00}\|^{-1}$ times the average over $\mathrm{GL}_2(\mathcal O_v)$ of the integral of $f$ along the coset $\gamma N$, with explicit normalising factors for $\tau$ and $\nu$. It is the local input for the hyperbolic terms in the local analysis of orbital integrals, and is used in the evaluation of orbital integrals of indicator functions at diagonal elements, in their invariance under central and scalar twists, and in the construction of locally constant compactly supported functions with prescribed orbital integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_eq_norm_inv_mul_integral_localIntegralSet_integral_conj_unipotentGL2_of_isOrbitalIntegral_of_diagonal.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain

theorem AutomorphicForm.eq_norm_inv_mul_integral_localIntegralSet_integral_conj_unipotentGL2_of_isOrbitalIntegral_of_diagonal
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (hγ₀₁ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0)
    (hγ₁₀ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0)
    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ)
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (ν : Measure (v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : AutomorphicForm.IsLocalTestFn K v f)
    (I : ℂ) (hI : AutomorphicForm.IsOrbitalIntegral K v γ τ f I) :
    I = (((τ {t : AutomorphicForm.localCentralizer K v γ |
              (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v}).toReal⁻¹ *
          (ν (v.adicCompletionIntegers K : Set (v.adicCompletion K))).toReal⁻¹ *
          ‖1 - (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 /
              (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0‖⁻¹ : ℝ) : ℂ) *
        (letI := AutomorphicForm.localGLBorel K v
         ∫ k, (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ)) k *
           (∫ u, f (k⁻¹ * (γ * AutomorphicForm.unipotentGL2 u) * k) ∂ν) ∂(AutomorphicForm.localHaar K v)) := by sorry
