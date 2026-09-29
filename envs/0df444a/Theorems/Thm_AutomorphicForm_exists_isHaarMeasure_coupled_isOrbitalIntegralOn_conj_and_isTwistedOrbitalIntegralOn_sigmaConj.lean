-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isHaarMeasure_coupled_isOrbitalIntegralOn_conj_and_isTwistedOrbitalIntegralOn_sigmaConj
-- name    : AutomorphicForm.exists_isHaarMeasure_coupled_isOrbitalIntegralOn_conj_and_isTwistedOrbitalIntegralOn_sigmaConj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/65aca3c2-c484-5712-a4b1-57d9da16fa13
-- title:
--   Conjugation transport of couplings and (twisted) orbital integrals
-- statement:
--   Let $L/K$ be a finite extension of fields, $A$ a commutative topological $K$-algebra whose topology makes it a topological ring, and $\sigma$ a $K$-algebra automorphism of $L$; all groups $\mathrm{GL}_2$ carry the Borel $\sigma$-algebra of their topology, $\mathrm{GL}_2(A)$ is mapped into $\mathrm{GL}_2(L\otimes_K A)$ by $a\mapsto 1\otimes a$ (`toTensorGL`), and $\sigma$ acts on $\mathrm{GL}_2(L\otimes_K A)$ entrywise through $\sigma\otimes\mathrm{id}$ (`sigmaGL`). Two assertions are made. First: for every left-translation-invariant measure $\mu_A$ on $\mathrm{GL}_2(A)$, all $\gamma,x\in\mathrm{GL}_2(A)$, every Haar measure $\tau$ on the centraliser of $\gamma$, and every $\gamma'=x^{-1}\gamma x$, there is a Haar measure $\tau_0$ on the centraliser of $\gamma'$ such that (i) for all $\delta,y\in\mathrm{GL}_2(L\otimes_K A)$ and all measures $\tau'$ on the $\sigma$-twisted centraliser $\{t: t\delta\sigma(t)^{-1}=\delta\}$ of $\delta$, if $\tau'$ and $\tau$ are coupled at $(\gamma,\delta,y)$ — the image of $\tau'$ under $t\mapsto y^{-1}ty$ equals the image of $\tau$ under $1\otimes(\cdot)$ — then $\tau'$ and $\tau_0$ are coupled at $(\gamma',\delta,y\,(1\otimes x))$; (ii) if $1\otimes\gamma=y^{-1}\big(\prod_{i<[L:K]}\sigma^i(\delta)\big)y$ then $1\otimes\gamma'=(y\,(1\otimes x))^{-1}\big(\prod_i\sigma^i(\delta)\big)(y\,(1\otimes x))$; (iii) every $I\in\mathbb{C}$ realised as $\int f(z^{-1}\gamma z)w(z)\,d\mu_A$ for a section function $w$ relative to $\tau$ is likewise realised at $\gamma'$ relative to $\tau_0$. Second: for every left-invariant $\mu$ on $\mathrm{GL}_2(L\otimes_K A)$, $\gamma\in\mathrm{GL}_2(A)$, $\delta,x\in\mathrm{GL}_2(L\otimes_K A)$, a measure $\tau$ on the centraliser of $\gamma$, a Haar measure $\tau'$ on the twisted centraliser of $\delta$ coupled with $\tau$ at $(\gamma,\delta,x)$, and $\delta'=x^{-1}\delta\sigma(x)$, there is a Haar measure $\tau_1$ on the twisted centraliser of $\delta'$ coupled with $\tau$ at $(\gamma,\delta',1)$ such that every value $I$ of the twisted orbital integral $\int \varphi(z^{-1}\delta\sigma(z))w(z)\,d\mu$, with $w$ satisfying `IsTwistedSectionFnOn` relative to $\tau'$, is also a value of the twisted orbital integral at $\delta'$ relative to $\tau_1$.
--
--   This packages the bookkeeping needed to compare orbital integrals on $\mathrm{GL}_2(A)$ with $\sigma$-twisted orbital integrals on $\mathrm{GL}_2(L\otimes_K A)$ in the style of base change for $\mathrm{GL}(2)$: conjugacy on the ordinary side and $\sigma$-conjugacy on the twisted side each transport the chosen Haar measures on (twisted) centralisers, the coupling between them, the norm-conjugator relation and the resulting integral values. It is used in the construction of test functions with matching twisted orbital integrals ([`AutomorphicForm.exists_contDiff_hasCompactSupport_forall_isTwistedOrbitalIntegralOn_conjAe_imp_eq`](thm.html#AutomorphicForm.exists_contDiff_hasCompactSupport_forall_isTwistedOrbitalIntegralOn_conjAe_imp_eq)), and its twisted half is obtained from [`AutomorphicForm.exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate`](thm.html#AutomorphicForm.exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isHaarMeasure_coupled_isOrbitalIntegralOn_conj_and_isTwistedOrbitalIntegralOn_sigmaConj.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem
AutomorphicForm.exists_isHaarMeasure_coupled_isOrbitalIntegralOn_conj_and_isTwistedOrbitalIntegralOn_sigmaConj
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
    (σ : L ≃ₐ[K] L) :
    (∀ (μA : @Measure (GL (Fin 2) A) (glBorelOf A)),
      (∀ g : GL (Fin 2) A, @Measure.map _ _ (glBorelOf A) (glBorelOf A) (fun z => g * z) μA = μA) →
      ∀ (γ x : GL (Fin 2) A)
        (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ)),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel A γ) τ →
        ∀ γ' : GL (Fin 2) A, γ' = x⁻¹ * γ * x →
          ∃ τ₀ : @Measure (Subgroup.centralizer ({γ'} : Set (GL (Fin 2) A))) (centralizerBorel A γ'),
            @Measure.IsHaarMeasure _ _ _ (centralizerBorel A γ') τ₀ ∧
            (∀ (δ y : GL (Fin 2) (L ⊗[K] A))
              (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ)),
              Coupled K L A σ γ δ y τ τ' → Coupled K L A σ γ' δ (y * toTensorGL K L A x) τ₀ τ') ∧
            (∀ δ y : GL (Fin 2) (L ⊗[K] A),
              IsNormConjugator K L A σ γ δ y → IsNormConjugator K L A σ γ' δ (y * toTensorGL K L A x)) ∧
            ∀ (f : GL (Fin 2) A → ℂ) (I : ℂ),
              IsOrbitalIntegralOn A μA γ τ f I → IsOrbitalIntegralOn A μA γ' τ₀ f I) ∧
    (∀ (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A))),
      (∀ g : GL (Fin 2) (L ⊗[K] A),
        @Measure.map _ _ (glBorelOf (L ⊗[K] A)) (glBorelOf (L ⊗[K] A)) (fun z => g * z) μ = μ) →
      ∀ (γ : GL (Fin 2) A) (δ x : GL (Fin 2) (L ⊗[K] A))
        (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
        (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ)),
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ δ) τ' →
        Coupled K L A σ γ δ x τ τ' →
        ∀ δ' : GL (Fin 2) (L ⊗[K] A), δ' = x⁻¹ * δ * sigmaGL K L A σ x →
          ∃ τ₁ : @Measure (twistedCentralizer K L A σ δ') (twistedCentralizerBorel K L A σ δ'),
            @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ δ') τ₁ ∧
            Coupled K L A σ γ δ' 1 τ τ₁ ∧
            ∀ (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (I : ℂ),
              IsTwistedOrbitalIntegralOn K L A σ μ δ τ' φ I →
                IsTwistedOrbitalIntegralOn K L A σ μ δ' τ₁ φ I) := by sorry
