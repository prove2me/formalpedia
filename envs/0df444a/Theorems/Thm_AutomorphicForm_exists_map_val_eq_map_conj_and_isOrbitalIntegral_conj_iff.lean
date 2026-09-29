-- Prove2me | Theorems.Thm_AutomorphicForm_exists_map_val_eq_map_conj_and_isOrbitalIntegral_conj_iff
-- name    : AutomorphicForm.exists_map_val_eq_map_conj_and_isOrbitalIntegral_conj_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/e774437e-e585-5bb8-a0de-eda695b3b46d
-- title:
--   Conjugation equivariance of local orbital integrals on GL₂(Kᵥ)
-- statement:
--   Let $K$ be a number field, $v$ a nonzero prime of $\mathcal{O}_K$, and $G = GL_2(K_v)$ the general linear group of degree $2$ over the $v$-adic completion, equipped with its Borel $\sigma$-algebra; for $\gamma \in G$ let $T_\gamma =$ `Subgroup.centralizer {\gamma}` carry its Borel $\sigma$-algebra. Given $\gamma, x \in G$ and a Borel measure $\tau$ on $T_\gamma$, the assertion is that there is a Borel measure $\tau'$ on $T_{x\gamma x^{-1}}$ such that: (1) the image of $\tau'$ under the inclusion $T_{x\gamma x^{-1}} \hookrightarrow G$ coincides with the image, under $g \mapsto xgx^{-1}$, of the image of $\tau$ under the inclusion $T_\gamma \hookrightarrow G$; (2) if $\tau$ is a Haar measure on $T_\gamma$, then $\tau'$ is a Haar measure on $T_{x\gamma x^{-1}}$; and (3) for every $f : G \to \mathbb{C}$ and every $I \in \mathbb{C}$, $I$ is an orbital-integral value of $f$ at $x\gamma x^{-1}$ relative to $\tau'$ if and only if it is one at $\gamma$ relative to $\tau$. Here, in the sense of `IsOrbitalIntegral`, $I$ is an orbital-integral value of $f$ at $\gamma$ relative to $\tau$ when there is a nonnegative, Borel measurable, compactly supported $w : G \to \mathbb{R}$ with $\int_{T_\gamma} w(ty)\,d\tau(t) = 1$ for every $y$ with $f(y^{-1}\gamma y) \neq 0$, and $I = \int_G f(y^{-1}\gamma y)\,w(y)\,d\mu_v(y)$ for the fixed Haar measure $\mu_v =$ `localHaar K v` on $G$, normalised to give mass one to a distinguished compact set.
--
--   This is the transport of local orbital integrals under conjugation of the element: the orbital integral depends only on the conjugacy class of $\gamma$, once the measure on the centraliser is transported by $t \mapsto xtx^{-1}$. It is used in the analysis of orbital integrals of local test functions near a given element, where conjugates of a fixed $\gamma$ must be compared.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_map_val_eq_map_conj_and_isOrbitalIntegral_conj_iff.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain

theorem AutomorphicForm.exists_map_val_eq_map_conj_and_isOrbitalIntegral_conj_iff
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ x : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ)) :
    ∃ τ' : @Measure (AutomorphicForm.localCentralizer K v (x * γ * x⁻¹))
        (AutomorphicForm.localCentralizerBorel K v (x * γ * x⁻¹)),
      @Measure.map _ _ (AutomorphicForm.localCentralizerBorel K v (x * γ * x⁻¹)) (AutomorphicForm.localGLBorel K v)
          Subtype.val τ' =
        @Measure.map _ _ (AutomorphicForm.localGLBorel K v) (AutomorphicForm.localGLBorel K v)
          (fun g : GL (Fin 2) (v.adicCompletion K) => x * g * x⁻¹)
          (@Measure.map _ _ (AutomorphicForm.localCentralizerBorel K v γ) (AutomorphicForm.localGLBorel K v)
            Subtype.val τ) ∧
      (@Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ →
        @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (x * γ * x⁻¹)) τ') ∧
      ∀ (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (I : ℂ),
        AutomorphicForm.IsOrbitalIntegral K v (x * γ * x⁻¹) τ' f I ↔
          AutomorphicForm.IsOrbitalIntegral K v γ τ f I := by sorry
