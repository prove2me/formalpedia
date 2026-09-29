-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isCompact_forall_ratio_mem_of_isOrbitalIntegral_scalar_mul_diagUnits2
-- name    : AutomorphicForm.exists_isCompact_forall_ratio_mem_of_isOrbitalIntegral_scalar_mul_diagUnits2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/f8e17b1b-0314-5dab-8dc5-9f391efb22cd
-- title:
--   Compactness of the ratio locus of non-vanishing orbital values
-- statement:
--   Let $K$ be a number field and $v$ a non-zero prime of its ring of integers $\mathcal{O}_K$, with completion $K_v$, and let $f_v : \mathrm{GL}_2(K_v) \to \mathbb{C}$ be a local test function, i.e. $f_v$ is locally constant and has compact support. Then there is a set $C \subseteq K_v^\times$, compact in the unit group, with the following property: for all $a, b \in K_v^\times$, writing $\gamma = b \cdot \mathrm{diag}(a,1)$ for the product of the scalar matrix with entry $b$ and the invertible diagonal matrix with entries $a$ and $1$, for every measure $\tau$ on the centraliser of $\{\gamma\}$ in $\mathrm{GL}_2(K_v)$ (equipped with its Borel $\sigma$-algebra) and every complex number $J$, if $J$ is an orbital-integral value of $f_v$ at $\gamma$ relative to $\tau$ — that is, there is a function $w : \mathrm{GL}_2(K_v) \to \mathbb{R}$ that is non-negative, measurable and compactly supported, satisfies $\int_{t \in Z(\gamma)} w(tx)\,d\tau = 1$ for every $x$ with $f_v(x^{-1}\gamma x) \neq 0$, and for which $J = \int f_v(x^{-1}\gamma x)\, w(x)\, d\mu$ with $\mu$ the Haar measure [`AutomorphicForm.localHaar`](def/AutomorphicForm_LocalOrbitalBase.html#L168) on $\mathrm{GL}_2(K_v)$ — and if $J \neq 0$, then $a \in C$. The compact set depends only on $K$, $v$ and $f_v$, uniformly in $b$, in $\tau$ and in the section function $w$.
--
--   This is the uniform support bound for local orbital integrals along the torus direction $\mathrm{diag}(a,1)$: non-vanishing of an orbital value confines the diagonal ratio $a$ to a fixed compact subset of $K_v^\times$, independently of the central parameter $b$. It is used in the cubic-induction part of the Langlands–Tunnell argument, where it feeds [`AutomorphicForm.exists_finset_forall_window_product_eq_zero_of_not_mem`](thm.html#AutomorphicForm.exists_finset_forall_window_product_eq_zero_of_not_mem) to make products of local orbital windows vanish outside a finite set.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isCompact_forall_ratio_mem_of_isOrbitalIntegral_scalar_mul_diagUnits2.lean

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

theorem AutomorphicForm.exists_isCompact_forall_ratio_mem_of_isOrbitalIntegral_scalar_mul_diagUnits2
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : AutomorphicForm.IsLocalTestFn K v fv) :
    ∃ C : Set (v.adicCompletion K)ˣ, IsCompact C ∧
      ∀ (a b : (v.adicCompletion K)ˣ)
        (τ : @Measure (AutomorphicForm.localCentralizer K v
              (Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1))
            (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1)))
        (J : ℂ),
        AutomorphicForm.IsOrbitalIntegral K v
            (Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1) τ fv J → J ≠ 0 → a ∈ C := by sorry
