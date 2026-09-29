-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime
-- name    : AutomorphicForm.exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/603cfd50-8177-515a-97da-32afa6126302
-- title:
--   Local transfer near a central norm at a finite place
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra whose degree $\operatorname{finrank}_K L$ is prime, let $\sigma$ be a $K$-automorphism of $L$ with $\sigma \neq 1$, let $v$ be a height-one prime of $\mathcal{O}_K$ with completion $K_v$, and assume there is no $K$-algebra map $L \to K_v$. Write $N\delta$ for `normString`, the product $\prod_{i<[L:K]}\sigma^{i}(\delta)$ computed through the action of $\sigma$ on the left factor of $L \otimes_K K_v$, and call $g \in \mathrm{GL}_2$ regular semisimple when $\operatorname{tr}(g)^2 - 4\det(g)$ is a unit. Let $\delta_0 \in \mathrm{GL}_2(L \otimes_K K_v)$ have $N\delta_0$ not regular semisimple, and let $c \in K_v^{\times}$ be such that the scalar matrix $c \cdot 1$ is a norm of $\delta_0$, i.e. its image in $\mathrm{GL}_2(L \otimes_K K_v)$ equals $y^{-1} (N\delta_0) y$ for some $y$. Then for every $\varphi_v : \mathrm{GL}_2(L \otimes_K K_v) \to \mathbb{C}$ that is locally constant with compact support there exist a locally constant, compactly supported $f_v : \mathrm{GL}_2(K_v) \to \mathbb{C}$ and a neighbourhood $V$ of $c \cdot 1$ in $\mathrm{GL}_2(K_v)$ such that: (A1) for every $\delta$ with $N\delta$ regular semisimple, every regular semisimple $\gamma \in V$, every $y$ with $\gamma = y^{-1}(N\delta)y$ in $\mathrm{GL}_2(L \otimes_K K_v)$, and all Haar measures $\tau$ on the centraliser of $\gamma$ and $\tau'$ on the $\sigma$-twisted centraliser of $\delta$ that are `Coupled` through $y$ (the pushforward of $\tau'$ along $t \mapsto y^{-1}ty$ agrees with the pushforward of $\tau$ along the base-change inclusion), any value $I'$ of the twisted orbital integral of $\varphi_v$ at $\delta$ for $\tau'$ and any value $I$ of the orbital integral of $f_v$ at $\gamma$ for $\tau$ satisfy $I' = I$; (A2) for every regular semisimple $\gamma \in V$ that is a norm of no $\delta$, every value of the orbital integral of $f_v$ at $\gamma$ for any Haar measure on the centraliser of $\gamma$ is $0$; and (B) the identity of (A1) also holds for the pair $(c \cdot 1, \delta_0)$ itself, for every $y$ realising $c \cdot 1$ as a norm of $\delta_0$ and every coupled pair of Haar measures. Here orbital integrals are taken in the `IsOrbitalIntegral`/`IsTwistedOrbitalIntegral` sense, namely as integrals of $x \mapsto f_v(x^{-1}\gamma x)$, resp. of the twisted conjugation integrand, against a nonnegative, measurable, compactly supported weight whose centraliser averages are $1$ on the relevant support.
--
--   This is the local transfer of test functions for cyclic base change of $\mathrm{GL}_2$ of prime degree, at a finite place where $L \otimes_K K_v$ is a field, localised near a scalar $c \cdot 1$ arising as the norm of a $\delta_0$ with singular norm string; since a scalar matrix is never regular semisimple, clause (A1) says nothing at $c \cdot 1$ and clause (B) supplies the matching of the twisted and untwisted integrals at that point. It feeds the global comparison of orbital integrals through [`AutomorphicForm.areMatchingLocal_central_transfer_and_eq_zero_of_not_exists_isNormOf`](thm.html#AutomorphicForm.areMatchingLocal_central_transfer_and_eq_zero_of_not_exists_isNormOf).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem
AutomorphicForm.exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K)) (hι : IsEmpty (L →ₐ[K] v.adicCompletion K))
    (δ₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ₀ : ¬ AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ δ₀))
    (c : (v.adicCompletion K)ˣ)
    (hc : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ₀) :
    ∀ φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ, AutomorphicForm.IsSemiLocalTestFn K L v φv →
      ∃ fv : GL (Fin 2) (v.adicCompletion K) → ℂ, AutomorphicForm.IsLocalTestFn K v fv ∧
        (∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
          (∀ δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
            AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ δ) →
            ∀ γ ∈ V, AutomorphicForm.IsRegularSemisimple γ →
            ∀ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
              AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ γ δ y →
            ∀ (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
              (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ)),
              @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ →
              @Measure.IsHaarMeasure _ _ _
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ' →
              AutomorphicForm.Coupled K L (v.adicCompletion K) σ γ δ y τ τ' →
              ∀ I I' : ℂ, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ τ' φv I' →
                AutomorphicForm.IsOrbitalIntegral K v γ τ fv I → I' = I) ∧
          (∀ γ ∈ V, AutomorphicForm.IsRegularSemisimple γ →
            (¬ ∃ δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
              AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ γ δ) →
            ∀ τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ),
              @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ →
              ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v γ τ fv I → I = 0)) ∧
        (∀ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
          AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ
            (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ₀ y →
          ∀ (τ : @Measure (AutomorphicForm.localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c))
              (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
            (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ₀)
              (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ₀)),
            @Measure.IsHaarMeasure _ _ _
              (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ →
            @Measure.IsHaarMeasure _ _ _
              (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ₀) τ' →
            AutomorphicForm.Coupled K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ₀ y τ τ' →
            ∀ I I' : ℂ, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ₀ τ' φv I' →
              AutomorphicForm.IsOrbitalIntegral K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ fv I →
                I' = I) := by sorry
