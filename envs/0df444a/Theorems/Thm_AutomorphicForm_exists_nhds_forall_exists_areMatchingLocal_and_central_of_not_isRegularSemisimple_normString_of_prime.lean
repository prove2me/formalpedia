-- Prove2me | Theorems.Thm_AutomorphicForm_exists_nhds_forall_exists_areMatchingLocal_and_central_of_not_isRegularSemisimple_normString_of_prime
-- name    : AutomorphicForm.exists_nhds_forall_exists_areMatchingLocal_and_central_of_not_isRegularSemisimple_normString_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/eef19311-8bf5-5372-acda-58970fb3c295
-- title:
--   Local transfer near a singular norm, with central identities
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra of prime degree $n = [L:K]$, let $\sigma \ne 1$ be a $K$-automorphism of $L$, and let $v$ be a nonzero prime of $\mathcal{O}_K$ such that there is no $K$-algebra map $L \to K_v$ into the $v$-adic completion. Write $\sigma$ also for the ring automorphism $\sigma \otimes \mathrm{id}$ of $L \otimes_K K_v$ and for the induced map `sigmaGL` on $GL_2(L \otimes_K K_v)$, and for $\delta$ in that group put $N(\delta) = \delta \cdot \sigma(\delta) \cdots \sigma^{n-1}(\delta)$ (`normString`); call an element of $GL_2$ over a commutative ring regular semisimple when $\mathrm{tr}^2 - 4\det$ is a unit. Let $\delta_0 \in GL_2(L \otimes_K K_v)$ be such that $N(\delta_0)$ is not regular semisimple. The assertion is that there is a neighbourhood $U$ of $\delta_0$ such that every locally constant, compactly supported $\varphi_v : GL_2(L \otimes_K K_v) \to \mathbb{C}$ with $\operatorname{tsupport} \varphi_v \subseteq U$ admits a locally constant, compactly supported $f_v : GL_2(K_v) \to \mathbb{C}$ with the following two groups of properties. First, $\varphi_v$ and $f_v$ match locally, with respect to the Haar measures `semiLocalHaar` on $GL_2(L \otimes_K K_v)$ and `localHaar` on $GL_2(K_v)$: for all $\delta$ with $N(\delta)$ regular semisimple, all regular semisimple $\gamma \in GL_2(K_v)$ and all $y$ with $\gamma \otimes 1 = y^{-1} N(\delta) y$, and all Haar measures $\tau$ on the centraliser of $\gamma$ and $\tau'$ on the $\sigma$-twisted centraliser $\{t : t\,\delta\,\sigma(t)^{-1} = \delta\}$ that are coupled (the image of $\tau'$ under $t \mapsto y^{-1} t y$ equals the image of $\tau$ under $t \mapsto t \otimes 1$), every twisted orbital integral of $\varphi_v$ at $\delta$ relative to $\tau'$ equals every orbital integral of $f_v$ at $\gamma$ relative to $\tau$; and for regular semisimple $\gamma$ that is not $N(\delta)$-conjugate to $\gamma \otimes 1$ for any $\delta$, all orbital integrals of $f_v$ at $\gamma$ vanish. Second, at central elements: for every unit $c_1$ of $K_v$, all $\delta_1, y$ with $(c_1 I_2) \otimes 1 = y^{-1} N(\delta_1) y$, and all coupled Haar measures $\tau$ on the centraliser of the scalar matrix $c_1 I_2$ and $\tau'$ on the twisted centraliser of $\delta_1$: (i) every twisted orbital integral of $\varphi_v$ at $\delta_1$ relative to $\tau'$ equals every orbital integral of $f_v$ at $c_1 I_2$ relative to $\tau$; (ii) if no $\delta$ in $\operatorname{tsupport}\varphi_v$ satisfies $(c_1 I_2) \otimes 1 = y^{-1} N(\delta) y$ for some $y$, then every orbital integral of $f_v$ at $c_1 I_2$ relative to $\tau$ is $0$; (iii) for every nonnegative, measurable, compactly supported $w' : GL_2(L \otimes_K K_v) \to \mathbb{R}$ with $\int_{t} w'(tx)\,d\tau' = 1$ whenever $\varphi_v(x^{-1}\delta_1\sigma(x)) \ne 0$, the function $x \mapsto \varphi_v(x^{-1}\delta_1\sigma(x))\,w'(x)$ is integrable for `semiLocalHaar`.
--
--   This is the local transfer statement for cyclic base change of $GL(2)$ of prime degree at a place $v$ that does not split in $L$, in the case of test functions concentrated near an element whose norm is not regular semisimple; the additional clauses record the behaviour of the transfer at the elements whose norm is central, together with the integrability needed for the corresponding twisted orbital integrals to be defined. It is used by [`AutomorphicForm.exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime`](thm.html#AutomorphicForm.exists_isLocalTestFn_areMatching_nhds_and_central_transfer_of_isNormOf_scalar_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_nhds_forall_exists_areMatchingLocal_and_central_of_not_isRegularSemisimple_normString_of_prime.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem
AutomorphicForm.exists_nhds_forall_exists_areMatchingLocal_and_central_of_not_isRegularSemisimple_normString_of_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K)) (hι : IsEmpty (L →ₐ[K] v.adicCompletion K))
    (δ₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ₀ : ¬ AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ δ₀)) :
    ∃ U ∈ nhds δ₀, ∀ φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ,
      AutomorphicForm.IsSemiLocalTestFn K L v φv → tsupport φv ⊆ U →
        ∃ fv : GL (Fin 2) (v.adicCompletion K) → ℂ,
          AutomorphicForm.IsLocalTestFn K v fv ∧ AutomorphicForm.AreMatchingLocal K L v σ φv fv ∧
          ∀ (c₁ : (v.adicCompletion K)ˣ) (δ₁ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
            AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ
              (Matrix.GeneralLinearGroup.scalar (Fin 2) c₁) δ₁ y →
            ∀ (τ : @Measure (AutomorphicForm.localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c₁))
                (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c₁)))
              (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ₁)
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ₁)),
              @Measure.IsHaarMeasure _ _ _
                (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c₁)) τ →
              @Measure.IsHaarMeasure _ _ _
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ₁) τ' →
              AutomorphicForm.Coupled K L (v.adicCompletion K) σ
                (Matrix.GeneralLinearGroup.scalar (Fin 2) c₁) δ₁ y τ τ' →
              (∀ I I' : ℂ, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ₁ τ' φv I' →
                AutomorphicForm.IsOrbitalIntegral K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c₁) τ fv I →
                  I' = I) ∧
              ((¬ ∃ δ ∈ tsupport φv, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ
                  (Matrix.GeneralLinearGroup.scalar (Fin 2) c₁) δ) →
                ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c₁) τ fv I →
                  I = 0) ∧
              (∀ w' : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ,
                AutomorphicForm.IsTwistedSectionFnOn K L (v.adicCompletion K) σ δ₁ τ' φv w' →
                Integrable
                  (fun x => φv (x⁻¹ * δ₁ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x) * (w' x : ℂ))
                  (AutomorphicForm.semiLocalHaar K L v)) := by sorry
