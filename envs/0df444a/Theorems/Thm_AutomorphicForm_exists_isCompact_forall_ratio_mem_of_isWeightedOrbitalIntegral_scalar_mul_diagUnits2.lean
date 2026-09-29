-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isCompact_forall_ratio_mem_of_isWeightedOrbitalIntegral_scalar_mul_diagUnits2
-- name    : AutomorphicForm.exists_isCompact_forall_ratio_mem_of_isWeightedOrbitalIntegral_scalar_mul_diagUnits2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/1fe14e6f-9f74-5dbd-a9a7-30f3ed9d9b93
-- title:
--   Compact support in the ratio a for weighted orbital values
-- statement:
--   Let $K$ be a number field, $v$ a nonzero prime of its ring of integers $\mathcal{O}_K$, and let $f_v \colon \mathrm{GL}_2(K_v) \to \mathbb{C}$ be a local test function on the general linear group over the completion $K_v$, meaning that $f_v$ is locally constant and has compact support. Then there is a subset $C$ of the unit group $K_v^\times$ which is compact and has the following property. Let $a, b \in K_v^\times$, put $\gamma = (b \cdot I_2)\,\mathrm{diag}(a,1)$, the product of the scalar matrix with entry $b$ and the invertible diagonal matrix `diagUnits2 a 1` with diagonal entries $a$ and $1$; let $\tau$ be any measure on the centraliser subgroup of $\{\gamma\}$ in $\mathrm{GL}_2(K_v)$, taken with its Borel $\sigma$-algebra, and let $J \in \mathbb{C}$. Suppose $J$ is a weighted orbital value of $f_v$ at $\gamma$ relative to $\tau$, that is, there is a function $s \colon \mathrm{GL}_2(K_v) \to \mathbb{R}$ satisfying the predicate `IsSectionFnOn` for the data $(\gamma, \tau, f_v)$ and such that $J = \int f_v(x^{-1}\gamma x)\,\mathrm{LocalWeight.weight}(x)\,s(x)\,d\mu(x)$, where $\mu$ is the Haar measure `localHaar` on $\mathrm{GL}_2(K_v)$ and $\mathrm{LocalWeight.weight}$ is the real-valued local weight factor. If $J \neq 0$, then $a \in C$. The compact set $C$ depends only on $K$, $v$ and $f_v$, uniformly in the central parameter $b$, in the measure $\tau$ and in the section function.
--
--   This is the local support bound for weighted orbital integrals in the direction of the diagonal ratio: non-vanishing of a weighted orbital value at $b\,\mathrm{diag}(a,1)$ confines $a$ to a fixed compact subset of $K_v^\times$, the conjugation invariant $\operatorname{tr}^2/\det$ of $b\,\mathrm{diag}(a,1)$ being $a + 2 + a^{-1}$, independent of $b$. It feeds the finiteness statement [`AutomorphicForm.exists_finset_forall_window_product_eq_zero_of_not_mem`](thm.html#AutomorphicForm.exists_finset_forall_window_product_eq_zero_of_not_mem), where only finitely many torus parameters can contribute to a product of local weighted terms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isCompact_forall_ratio_mem_of_isWeightedOrbitalIntegral_scalar_mul_diagUnits2.lean

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

theorem AutomorphicForm.exists_isCompact_forall_ratio_mem_of_isWeightedOrbitalIntegral_scalar_mul_diagUnits2
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : AutomorphicForm.IsLocalTestFn K v fv) :
    ∃ C : Set (v.adicCompletion K)ˣ, IsCompact C ∧
      ∀ (a b : (v.adicCompletion K)ˣ)
        (τ : @Measure (AutomorphicForm.localCentralizer K v
              (Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1))
            (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1)))
        (J : ℂ),
        AutomorphicForm.IsWeightedOrbitalIntegral K v
            (Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1) τ fv J → J ≠ 0 → a ∈ C := by sorry
