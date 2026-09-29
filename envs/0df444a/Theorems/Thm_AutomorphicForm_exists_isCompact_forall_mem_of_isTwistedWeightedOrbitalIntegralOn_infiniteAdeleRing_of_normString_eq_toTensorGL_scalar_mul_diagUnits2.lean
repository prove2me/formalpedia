-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isCompact_forall_mem_of_isTwistedWeightedOrbitalIntegralOn_infiniteAdeleRing_of_normString_eq_toTensorGL_scalar_mul_diagUnits2
-- name    : AutomorphicForm.exists_isCompact_forall_mem_of_isTwistedWeightedOrbitalIntegralOn_infiniteAdeleRing_of_normString_eq_toTensorGL_scalar_mul_diagUnits2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/579577f1-6aaf-5bb0-bd92-0f348281f81b
-- title:
--   Compactness of the b-locus for archimedean twisted orbital integrals
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $\sigma$ be a $K$-algebra automorphism of $L$, write $K_\infty$ for the infinite adele ring of $K$ and $E := L \otimes_K K_\infty$, and let $\sigma_{GL}$ denote the automorphism of $GL_2(E)$ obtained by applying $\sigma \otimes \mathrm{id}$ entrywise. Fix a unit $a \in K_\infty^\times$, an arbitrary measure $\mu$ on $GL_2(E)$ for its Borel structure, an arbitrary weight function $wt : GL_2(E) \to \mathbb{R}$, and a function $\varphi : GL_2(E) \to \mathbb{C}$ with compact support. Then there is a compact set $C \subseteq K_\infty^\times$ with the following property. Let $b \in K_\infty^\times$ and $\delta \in GL_2(E)$ be such that the norm string $\prod_{i=0}^{[L:K]-1} \sigma_{GL}^{i}(\delta)$ (the product of the iterates $\sigma_{GL}^{[i]}(\delta)$ for $i$ in $\mathrm{range}\,(\operatorname{finrank}_K L)$, in that order) equals the image under $GL_2(K_\infty) \to GL_2(E)$, induced by $x \mapsto 1 \otimes x$, of $b \cdot I_2$ times $\mathrm{diag}(a,1)$. Let $\tau'$ be any measure on the twisted centraliser $\{t \in GL_2(E) : t\,\delta\,\sigma_{GL}(t)^{-1} = \delta\}$ with its Borel structure, and let $J \in \mathbb{C}$ be a value of the twisted weighted orbital integral relation for these data, i.e. there exists $s : GL_2(E) \to \mathbb{R}$ which is non-negative, measurable and compactly supported, satisfies $\int_{t} s(tx)\,d\tau' = 1$ for every $x$ with $\varphi(x^{-1}\delta\,\sigma_{GL}(x)) \neq 0$, and for which $J = \int \varphi(x^{-1}\delta\,\sigma_{GL}(x))\, wt(x)\, s(x)\, d\mu$. If $J \neq 0$ then $b \in C$.
--
--   This is the archimedean instance of the support bound for twisted weighted orbital integrals along the split family $\delta$ with norm string $b\cdot\mathrm{diag}(a,1)$: non-vanishing of the integral confines the scalar parameter $b$ to a fixed compact subset of $K_\infty^\times$, uniformly in $\delta$, in the centraliser measure and in the auxiliary section function. It is used in the construction of a continuous compactly supported test function matching these archimedean twisted weighted orbital integrals, in the comparison of twisted and untwisted trace formulae for $GL_2$ underlying base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isCompact_forall_mem_of_isTwistedWeightedOrbitalIntegralOn_infiniteAdeleRing_of_normString_eq_toTensorGL_scalar_mul_diagUnits2.lean

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

theorem AutomorphicForm.exists_isCompact_forall_mem_of_isTwistedWeightedOrbitalIntegralOn_infiniteAdeleRing_of_normString_eq_toTensorGL_scalar_mul_diagUnits2
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (a : (InfiniteAdeleRing K)ˣ)
    (μ : @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)))
    (wt : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ)
    (φ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ) (hφ : HasCompactSupport φ) :
    ∃ C : Set (InfiniteAdeleRing K)ˣ, IsCompact C ∧
      ∀ (b : (InfiniteAdeleRing K)ˣ) (δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
        AutomorphicForm.normString K L (InfiniteAdeleRing K) σ δ =
          AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K)
            (Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1) →
        ∀ (τ' : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ)) (J : ℂ),
          AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ μ wt δ τ' φ J →
            J ≠ 0 → b ∈ C := by sorry
