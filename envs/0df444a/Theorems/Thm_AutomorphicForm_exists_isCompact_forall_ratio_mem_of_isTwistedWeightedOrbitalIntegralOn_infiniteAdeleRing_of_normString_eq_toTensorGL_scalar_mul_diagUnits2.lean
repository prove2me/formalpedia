-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isCompact_forall_ratio_mem_of_isTwistedWeightedOrbitalIntegralOn_infiniteAdeleRing_of_normString_eq_toTensorGL_scalar_mul_diagUnits2
-- name    : AutomorphicForm.exists_isCompact_forall_ratio_mem_of_isTwistedWeightedOrbitalIntegralOn_infiniteAdeleRing_of_normString_eq_toTensorGL_scalar_mul_diagUnits2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/c88bdc56-3050-5f62-8e63-6d576f114dd9
-- title:
--   Compactness of the a-support of archimedean twisted orbital values
-- statement:
--   Let $K \subseteq L$ be number fields with $L$ a $K$-algebra, let $\sigma$ be a $K$-algebra automorphism of $L$, write $K_\infty =$ `InfiniteAdeleRing K` and $G = \mathrm{GL}_2(L \otimes_K K_\infty)$ with its Borel $\sigma$-algebra coming from the topology. Let $\mu$ be a measure on $G$, let $wt : G \to \mathbb{R}$ be a weight function, and let $\varphi : G \to \mathbb{C}$ have compact support. The assertion is that there is a compact set $C \subseteq K_\infty^\times$, depending only on these data, with the following property: for all units $a, b \in K_\infty^\times$ and all $\delta \in G$ whose norm string $\prod_{i=0}^{[L:K]-1} \sigma^i(\delta)$ — the ordered product of the iterates of $\delta$ under the map of $G$ induced by $\sigma$ on $L \otimes_K K_\infty$ — equals the image under $\mathrm{GL}_2(K_\infty) \to G$ of $b \cdot I_2 \cdot \mathrm{diag}(a,1) = \mathrm{diag}(ab, b)$, and for every measure $\tau'$ on the twisted centralizer $\{t \in G : t\,\delta\,\sigma(t)^{-1} = \delta\}$ (again with its Borel $\sigma$-algebra) and every $J \in \mathbb{C}$ admitting a section function, i.e. a map $s : G \to \mathbb{R}$ that is non-negative, measurable, compactly supported and satisfies $\int_{t} s(tx)\,d\tau' = 1$ for every $x$ with $\varphi(x^{-1}\delta\,\sigma(x)) \neq 0$, and for which $J = \int_G \varphi(x^{-1}\delta\,\sigma(x))\, wt(x)\, s(x)\, d\mu$, one has: if $J \neq 0$ then $a \in C$.
--
--   This is the archimedean boundedness statement for twisted weighted orbital integrals: non-vanishing of such an integral at an element whose norm string is a scalar multiple of $\mathrm{diag}(a,1)$ confines the ratio $a$ to a compact subset of $K_\infty^\times$ determined by the test function alone. It is used by [`AutomorphicForm.exists_finset_forall_window_product_eq_zero_of_not_mem`](thm.html#AutomorphicForm.exists_finset_forall_window_product_eq_zero_of_not_mem) to make the corresponding family of twisted orbital contributions finitely supported.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isCompact_forall_ratio_mem_of_isTwistedWeightedOrbitalIntegralOn_infiniteAdeleRing_of_normString_eq_toTensorGL_scalar_mul_diagUnits2.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isCompact_forall_ratio_mem_of_isTwistedWeightedOrbitalIntegralOn_infiniteAdeleRing_of_normString_eq_toTensorGL_scalar_mul_diagUnits2
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L)
    (μ : @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)))
    (wt : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ)
    (φ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ) (hφ : HasCompactSupport φ) :
    ∃ C : Set (InfiniteAdeleRing K)ˣ, IsCompact C ∧
      ∀ (a b : (InfiniteAdeleRing K)ˣ) (δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
        AutomorphicForm.normString K L (InfiniteAdeleRing K) σ δ =
          AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K)
            (Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1) →
        ∀ (τ' : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ)) (J : ℂ),
          AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ μ wt δ τ' φ J →
            J ≠ 0 → a ∈ C := by sorry
