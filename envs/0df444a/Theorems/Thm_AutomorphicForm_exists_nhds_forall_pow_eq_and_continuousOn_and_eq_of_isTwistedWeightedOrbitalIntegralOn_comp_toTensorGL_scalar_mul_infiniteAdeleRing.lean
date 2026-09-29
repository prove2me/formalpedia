-- Prove2me | Theorems.Thm_AutomorphicForm_exists_nhds_forall_pow_eq_and_continuousOn_and_eq_of_isTwistedWeightedOrbitalIntegralOn_comp_toTensorGL_scalar_mul_infiniteAdeleRing
-- name    : AutomorphicForm.exists_nhds_forall_pow_eq_and_continuousOn_and_eq_of_isTwistedWeightedOrbitalIntegralOn_comp_toTensorGL_scalar_mul_infiniteAdeleRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/a52f42e5-951f-5a5b-871b-71176138feec
-- title:
--   Archimedean twisted weighted orbital integrals along a central direction
-- statement:
--   Let $K$ and $L$ be number fields with $L/K$ Galois, and let $\sigma$ be an element of $\mathrm{Gal}(L/K)$ such that every $\tau$ lies in the subgroup of integer powers of $\sigma$ (so $L/K$ is cyclic with generator $\sigma$); write $\ell = \operatorname{finrank}_K L$, $K_\infty =$ `InfiniteAdeleRing K` and $E = L \otimes_K K_\infty$. Let $\mu$ be a Haar measure on $GL_2(E)$ for the Borel $\sigma$-algebra of its topology, let $wt : GL_2(E) \to \mathbb{R}$ be continuous and satisfy $wt(tx) = wt(x)$ whenever the $(0,1)$ and $(1,0)$ entries of $t$ vanish, and let $\gamma \in GL_2(K_\infty)$ have vanishing $(0,1)$ and $(1,0)$ entries and be regular semisimple in the sense that $\operatorname{tr}(\gamma)^2 - 4\det(\gamma)$ is a unit. Let $\delta \in GL_2(E)$ satisfy the norm condition $\prod_{i<\ell} \sigma_{GL}^{i}(\delta) = \gamma \otimes 1$, where $\sigma_{GL}$ acts entrywise through $\sigma \otimes \mathrm{id}$ and $\gamma \otimes 1$ is the image of $\gamma$ under the entrywise map induced by $a \mapsto 1 \otimes a$. Let $\tau'$ be a Haar measure on the twisted centralizer $\{t : t\delta\sigma_{GL}(t)^{-1} = \delta\}$ (Borel $\sigma$-algebra), and let $\varphi : GL_2(E) \to \mathbb{C}$ be continuous with compact support. The conclusion asserts the existence of a neighbourhood $W$ of $1$ in $K_\infty$, a map $\rho : K_\infty \to K_\infty^{\times}$ and a function $g : K_\infty \to \mathbb{C}$ such that $\rho(1) = 1$, $\rho(\varepsilon)^{\ell} = \varepsilon$ for all $\varepsilon \in W$, both $\varepsilon \mapsto \rho(\varepsilon)$ and $g$ are continuous on $W$, and for every $\varepsilon \in W$ and every $J \in \mathbb{C}$: if $J$ is a twisted weighted orbital integral value for the translated test function $\varphi_\varepsilon(y) = \varphi\bigl((\rho(\varepsilon) I_2 \otimes 1) \, y\bigr)$, i.e. there is $s : GL_2(E) \to \mathbb{R}$ which is non-negative, measurable, compactly supported, satisfies $\int_{t} s(tx)\,d\tau' = 1$ for every $x$ with $\varphi_\varepsilon(x^{-1}\delta\sigma_{GL}(x)) \neq 0$, and for which $J = \int \varphi_\varepsilon(x^{-1}\delta\sigma_{GL}(x))\, wt(x)\, s(x)\, d\mu$, then $J = g(\varepsilon)$. Nothing is claimed about the existence of such a $J$.
--
--   This is the archimedean continuity statement for twisted weighted orbital integrals in the central direction: along a continuously varying family of $\ell$-th roots $\rho(\varepsilon)$ of $\varepsilon$ near $1$, all values of the twisted weighted orbital relation for the centrally translated test function are pinned to a single function of $\varepsilon$ that is continuous near $1$. It combines uniqueness of such values at a norm-regular-semisimple $\delta$ with the existence of continuous twisted section functions over the infinite adeles, and feeds the comparison of twisted weighted orbital integrals at diagonal central translates used in the base-change argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_nhds_forall_pow_eq_and_continuousOn_and_eq_of_isTwistedWeightedOrbitalIntegralOn_comp_toTensorGL_scalar_mul_infiniteAdeleRing.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_nhds_forall_pow_eq_and_continuousOn_and_eq_of_isTwistedWeightedOrbitalIntegralOn_comp_toTensorGL_scalar_mul_infiniteAdeleRing
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (μ : @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) _ _
      (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)) μ)
    (wt : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ) (hwtc : Continuous wt)
    (hwt : ∀ t x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
      (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 1 = 0 →
      (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 1 0 = 0 → wt (t * x) = wt x)
    (γ : GL (Fin 2) (InfiniteAdeleRing K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (hγ₀₁ : (γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 1 = 0)
    (hγ₁₀ : (γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0 = 0)
    (δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hδ : AutomorphicForm.normString K L (InfiniteAdeleRing K) σ δ = AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) γ)
    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ)) (hτ' : τ'.IsHaarMeasure)
    (φ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) :
    ∃ W ∈ nhds (1 : InfiniteAdeleRing K), ∃ ρ : InfiniteAdeleRing K → (InfiniteAdeleRing K)ˣ, ∃ g : InfiniteAdeleRing K → ℂ,
      ((ρ 1 : InfiniteAdeleRing K) = 1) ∧
      (∀ ε ∈ W, ((ρ ε : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) ^ Module.finrank K L = ε) ∧
      ContinuousOn (fun ε => ((ρ ε : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) W ∧
      ContinuousOn g W ∧
      ∀ ε ∈ W, ∀ J : ℂ,
        AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ μ wt δ τ'
          (fun y => φ (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K)
            (Matrix.GeneralLinearGroup.scalar (Fin 2) (ρ ε)) * y)) J →
        J = g ε := by sorry
