-- Prove2me | Theorems.Thm_AutomorphicForm_isOrbitalIntegral_scalar_mul_and_isWeightedOrbitalIntegral_scalar_mul_of_comp_scalar_mul
-- name    : AutomorphicForm.isOrbitalIntegral_scalar_mul_and_isWeightedOrbitalIntegral_scalar_mul_of_comp_scalar_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/ecc5a3b7-b636-5137-8c0a-574f37dd821e
-- title:
--   Central scalar translation of local orbital integrals
-- statement:
--   Let $K$ be a number field, $v$ a nonzero prime of $\mathcal{O}_K$, and write $K_v$ for the completion of $K$ at $v$. Given $\gamma \in GL_2(K_v)$, a unit $c \in K_v^\times$, a Haar measure $\tau$ on the centraliser $\mathrm{Cent}(\{\gamma\}) \le GL_2(K_v)$ for its Borel $\sigma$-algebra, normalised so that the set of elements of the centraliser lying in [`AutomorphicForm.localIntegralSet K v`](def/AutomorphicForm_LocalOrbitalBase.html#L100) (the matrices with entries in $\mathcal{O}_v$ whose inverse is again integral) has $\tau$-measure $1$, and likewise a Haar measure $\tau''$ on $\mathrm{Cent}(\{\mathrm{scalar}(c)\,\gamma\})$ with the same unit normalisation, and given an arbitrary function $f_v : GL_2(K_v) \to \mathbb{C}$, the following two implications hold. First, for every $I \in \mathbb{C}$: if there is a nonnegative Borel measurable $w$ of compact support on $GL_2(K_v)$ with $\int_{\mathrm{Cent}(\{\gamma\})} w(tx)\, d\tau(t) = 1$ whenever $f_v(c\,x^{-1}\gamma x) \neq 0$, and $I = \int f_v(c\,x^{-1}\gamma x)\, w(x)\, d\,$`localHaar K v`, then the same value $I$ is realised in this shape for $f_v$ at $\mathrm{scalar}(c)\,\gamma$ with the measure $\tau''$. Second, the analogous implication for every $J \in \mathbb{C}$ with the integrand weighted by the local height factor $2\log\bigl(\max(\|x_{00}\|,\|x_{01}\|)\cdot \mathrm{rowMaxNorm}(x)/\|\det x\|\bigr)$ evaluated at $x$.
--
--   This is the local absorption of a central scalar translate: replacing the conjugacy class $\gamma$ by $c\gamma$ is compensated by precomposing the test function with multiplication by the central scalar $c$, for both the plain and the height-weighted orbital integrals at $v$. It is used in the construction of locally constant compactly supported test functions with prescribed weighted orbital integrals at central-scalar multiples of diagonal classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isOrbitalIntegral_scalar_mul_and_isWeightedOrbitalIntegral_scalar_mul_of_comp_scalar_mul.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem AutomorphicForm.isOrbitalIntegral_scalar_mul_and_isWeightedOrbitalIntegral_scalar_mul_of_comp_scalar_mul
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K)) (c : (v.adicCompletion K)ˣ)
    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ)
    (hτ1 : τ (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (τ'' : @Measure (AutomorphicForm.localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c * γ))
        (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c * γ)))
    (hτ'' : @Measure.IsHaarMeasure _ _ _
        (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c * γ)) τ'')
    (hτ''1 : τ'' (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) :
    (∀ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v γ τ
        (fun x => fv (Matrix.GeneralLinearGroup.scalar (Fin 2) c * x)) I →
      AutomorphicForm.IsOrbitalIntegral K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c * γ) τ'' fv I) ∧
    (∀ J : ℂ, AutomorphicForm.IsWeightedOrbitalIntegral K v γ τ
        (fun x => fv (Matrix.GeneralLinearGroup.scalar (Fin 2) c * x)) J →
      AutomorphicForm.IsWeightedOrbitalIntegral K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c * γ) τ'' fv J) := by sorry
