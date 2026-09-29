-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate
-- name    : AutomorphicForm.exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/44830d18-da02-56d2-a766-57ddf60a8a65
-- title:
--   Transport of coupled twisted orbital data along σ-conjugation
-- statement:
--   Let $L/K$ be a finite extension of fields, $A$ a commutative topological $K$-algebra (with topological ring structure), $\sigma$ a $K$-automorphism of $L$, and write $G = \mathrm{GL}_2(L \otimes_K A)$ with its Borel $\sigma$-algebra; let $\sigma_{\mathrm{GL}}$ denote the endomorphism of $G$ induced by $\sigma \otimes \mathrm{id}_A$, and for $\delta \in G$ let $T_\delta = \{t \in G : t\,\delta\,\sigma_{\mathrm{GL}}(t)^{-1} = \delta\}$, again Borel. Let $\mu$ be a measure on $G$ invariant under every left translation $z \mapsto g z$. Let $\gamma \in \mathrm{GL}_2(A)$, let $\delta, x \in G$, let $\tau$ be a measure on the centralizer of $\gamma$ in $\mathrm{GL}_2(A)$ and $\tau'$ a Haar measure on $T_\delta$, and assume the coupling through $x$: the push-forward of $\tau'$ under $t \mapsto x^{-1} t x$ equals the push-forward of $\tau$ under the map $\mathrm{GL}_2(A) \to G$ induced by $a \mapsto 1 \otimes a$. Put $\delta' = x^{-1}\,\delta\,\sigma_{\mathrm{GL}}(x)$. Then there is a Haar measure $\tau_1$ on $T_{\delta'}$ which is coupled to $\tau$ through $1$, i.e. the push-forward of $\tau_1$ under $t \mapsto t$ equals the push-forward of $\tau$ under the same embedding, and such that for all $\varphi : G \to \mathbb{C}$ and $I \in \mathbb{C}$: if $I$ is a $\sigma$-twisted orbital integral of $\varphi$ at $\delta'$ relative to $\tau_1$ and $\mu$ — that is, $I = \int_G \varphi(g^{-1}\delta'\sigma_{\mathrm{GL}}(g))\,w(g)\,d\mu$ for some non-negative measurable compactly supported $w$ with $\int_{T_{\delta'}} w(tg)\,d\tau_1 = 1$ whenever $\varphi(g^{-1}\delta'\sigma_{\mathrm{GL}}(g)) \neq 0$ — then $I$ is likewise a $\sigma$-twisted orbital integral of $\varphi$ at $\delta$ relative to $\tau'$ and $\mu$.
--
--   This is the change-of-representative statement for $\sigma$-twisted orbital integrals: within a $\sigma$-conjugacy class one may normalise the representative to $\delta' = x^{-1}\delta\sigma(x)$, with the twisted centralizer measure transported accordingly and the coupling to the centralizer of $\gamma$ in $\mathrm{GL}_2(A)$ taken at the identity. It is used in the construction of matching local Hecke data at inert primes and in the existence statements for twisted orbital integrals and archimedean test factors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
    (σ : L ≃ₐ[K] L)
    (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (AutomorphicForm.glBorelOf (L ⊗[K] A)))
    (hμ : ∀ g : GL (Fin 2) (L ⊗[K] A),
      @Measure.map _ _ (AutomorphicForm.glBorelOf (L ⊗[K] A)) (AutomorphicForm.glBorelOf (L ⊗[K] A))
        (fun z => g * z) μ = μ)
    (γ : GL (Fin 2) A) (δ x : GL (Fin 2) (L ⊗[K] A))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (AutomorphicForm.centralizerBorel A γ))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L A σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L A σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L A σ δ) τ')
    (hC : AutomorphicForm.Coupled K L A σ γ δ x τ τ') :
    ∃ τ₁ : @Measure (AutomorphicForm.twistedCentralizer K L A σ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ x))
        (AutomorphicForm.twistedCentralizerBorel K L A σ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ x)),
      @Measure.IsHaarMeasure _ _ _
          (AutomorphicForm.twistedCentralizerBorel K L A σ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ x)) τ₁ ∧
        AutomorphicForm.Coupled K L A σ γ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ x) 1 τ τ₁ ∧
        ∀ (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (I : ℂ),
          AutomorphicForm.IsTwistedOrbitalIntegralOn K L A σ μ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ x) τ₁
              φ I →
            AutomorphicForm.IsTwistedOrbitalIntegralOn K L A σ μ δ τ' φ I := by sorry
