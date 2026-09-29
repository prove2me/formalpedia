-- Prove2me | Theorems.Thm_AutomorphicForm_exists_germ_forall_isOrbitalIntegral_eq_add_nhds_scalar_of_isLocalTestFn
-- name    : AutomorphicForm.exists_germ_forall_isOrbitalIntegral_eq_add_nhds_scalar_of_isLocalTestFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/3e43a4c8-ae80-521e-aac0-63292ab3954f
-- title:
--   Shalika germ expansion at a scalar on GL₂(Kᵥ)
-- statement:
--   Let $K$ be a number field, $v$ a height-one prime of $\mathcal{O}_K$ with completion $K_v$, and $c \in K_v^{\times}$; write $z = c\cdot 1$ for the corresponding scalar element of $\mathrm{GL}_2(K_v)$. The assertion is that there is a single functional $\nu$ on complex-valued functions on $\mathrm{GL}_2(K_v)$, depending only on $K$, $v$ and $c$, with the following property. For every $\gamma_0 \in \mathrm{GL}_2(K_v)$ that is regular semisimple in the sense that $\operatorname{tr}(\gamma_0)^2 - 4\det(\gamma_0)$ is a unit of $K_v$, and for every Borel measure $\nu_T$ on $\mathrm{GL}_2(K_v)$, there are a constant $A \in \mathbb{C}$ and a function $B : \mathrm{GL}_2(K_v) \to \mathbb{C}$, neither depending on a test function, such that: (i) for every locally constant, compactly supported $f : \mathrm{GL}_2(K_v) \to \mathbb{C}$ there is a neighbourhood $W$ of $z$ such that for all $\gamma \in W$ lying in the centraliser of $\{\gamma_0\}$ and regular semisimple in the same sense, every Haar measure $\tau$ on that centraliser of $\gamma$ whose image under the inclusion $\gamma$-centraliser $\hookrightarrow \mathrm{GL}_2(K_v)$ is $\nu_T$, and every $I \in \mathbb{C}$ representing the orbital integral of $f$ at $\gamma$ relative to $\tau$ — that is, $I = \int f(x^{-1}\gamma x) w(x)\,d\mu(x)$ for the fixed Haar measure $\mu$ on $\mathrm{GL}_2(K_v)$ and some nonnegative measurable compactly supported $w$ satisfying $\int_{\mathrm{Cent}(\gamma)} w(tx)\,d\tau(t) = 1$ whenever $f(x^{-1}\gamma x) \neq 0$ — one has $I = A\,f(z) + B(\gamma)\,\nu(f)$; (ii) if the off-diagonal entries of $\gamma_0$ vanish and the pullback of $\nu_T$ to the centraliser of $\gamma_0$ along the inclusion is a Haar measure, then $A = 0$ and on some neighbourhood of $z$ one has $B(\gamma) \neq 0$ for all regular semisimple $\gamma$ in that centraliser; (iii) if no conjugate $g^{-1}\gamma_0 g$ has both off-diagonal entries zero, and the same pullback is a Haar measure, then $A \neq 0$.
--
--   This is the Shalika germ expansion for $\mathrm{GL}_2$ at a central element, where only the two nilpotent orbits $\{0\}$ and the regular one contribute, stated uniformly in the test function: the germs $A$ and $B$ are fixed before $f$ is chosen, and the split/elliptic dichotomy records the vanishing of $A$ and nonvanishing of $B$ on a split torus and the nonvanishing of $A$ on an elliptic one. It feeds the comparison of twisted and ordinary orbital integrals at a scalar used in the finite-place quaternionic central pairing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_germ_forall_isOrbitalIntegral_eq_add_nhds_scalar_of_isLocalTestFn.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.exists_germ_forall_isOrbitalIntegral_eq_add_nhds_scalar_of_isLocalTestFn
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ) :
    ∃ ν : (GL (Fin 2) (v.adicCompletion K) → ℂ) → ℂ,
      ∀ (γ₀ : GL (Fin 2) (v.adicCompletion K)), AutomorphicForm.IsRegularSemisimple γ₀ →
      ∀ (νT : @Measure (GL (Fin 2) (v.adicCompletion K)) (AutomorphicForm.localGLBorel K v)),
      ∃ (A : ℂ) (B : GL (Fin 2) (v.adicCompletion K) → ℂ),

        (∀ (f : GL (Fin 2) (v.adicCompletion K) → ℂ), AutomorphicForm.IsLocalTestFn K v f →
          letI := AutomorphicForm.localGLBorel K v
          ∃ W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
            ∀ γ ∈ W, γ ∈ AutomorphicForm.localCentralizer K v γ₀ → AutomorphicForm.IsRegularSemisimple γ →
            ∀ (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ)),
              @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ →
              @Measure.map _ _ (AutomorphicForm.localCentralizerBorel K v γ) (AutomorphicForm.localGLBorel K v)
                  Subtype.val τ = νT →
              ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v γ τ f I →
                I = A * f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) + B γ * ν f) ∧

        (((γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
            (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0) →
          (@Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ₀)
              (@Measure.comap _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) (AutomorphicForm.localGLBorel K v)
                Subtype.val νT)) →
          A = 0 ∧
          letI := AutomorphicForm.localGLBorel K v
          ∃ W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
            ∀ γ ∈ W, γ ∈ AutomorphicForm.localCentralizer K v γ₀ → AutomorphicForm.IsRegularSemisimple γ → B γ ≠ 0) ∧

        ((∀ g : GL (Fin 2) (v.adicCompletion K),
            ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
               ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0)) →
          (@Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ₀)
              (@Measure.comap _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) (AutomorphicForm.localGLBorel K v)
                Subtype.val νT)) →
          A ≠ 0) := by sorry
