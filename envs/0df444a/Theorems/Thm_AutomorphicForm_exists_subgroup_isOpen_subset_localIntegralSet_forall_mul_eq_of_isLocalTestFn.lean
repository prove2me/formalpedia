-- Prove2me | Theorems.Thm_AutomorphicForm_exists_subgroup_isOpen_subset_localIntegralSet_forall_mul_eq_of_isLocalTestFn
-- name    : AutomorphicForm.exists_subgroup_isOpen_subset_localIntegralSet_forall_mul_eq_of_isLocalTestFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/af189f98-5047-5a76-ac4e-65575e297c6f
-- title:
--   Local test functions are bi-invariant under an open subgroup
-- statement:
--   Let $K$ be a number field and let $v$ be a nonzero prime of its ring of integers $\mathcal{O}_K$ (a point of the height-one spectrum), and write $K_v$ for the $v$-adic completion of $K$ and $\mathcal{O}_v$ for its valuation subring. Let $f_v : \mathrm{GL}_2(K_v) \to \mathbb{C}$ be a local test function, that is, $f_v$ is locally constant and has compact support. The assertion is that there exists a subgroup $U \le \mathrm{GL}_2(K_v)$ with the following three properties: $U$ is open as a subset of $\mathrm{GL}_2(K_v)$; $U$ is contained in the set of those $g \in \mathrm{GL}_2(K_v)$ for which both the matrix of $g$ and the matrix of $g^{-1}$ lie in `integralMatrixSet` of the subset $\mathcal{O}_v \subseteq K_v$ (the integrality condition on entries attached to that subset); and $f_v$ is bi-invariant under $U$, i.e. $f_v(u_1 g u_2) = f_v(g)$ for every $g \in \mathrm{GL}_2(K_v)$ and all $u_1, u_2 \in U$.
--
--   This is the standard smoothness statement for test functions on $\mathrm{GL}_2$ over a non-archimedean local field: a locally constant compactly supported function is bi-invariant under some compact open subgroup, here one sitting inside the integral points $\mathrm{GL}_2(\mathcal{O}_v)$. It is used in the local orbital-integral computations, where bi-invariance reduces integrals over orbits to finite sums over cosets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_subgroup_isOpen_subset_localIntegralSet_forall_mul_eq_of_isLocalTestFn.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain

theorem AutomorphicForm.exists_subgroup_isOpen_subset_localIntegralSet_forall_mul_eq_of_isLocalTestFn
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : AutomorphicForm.IsLocalTestFn K v fv) :
    ∃ U : Subgroup (GL (Fin 2) (v.adicCompletion K)), IsOpen (U : Set (GL (Fin 2) (v.adicCompletion K))) ∧
      (U : Set (GL (Fin 2) (v.adicCompletion K))) ⊆ AutomorphicForm.localIntegralSet K v ∧
      ∀ g : GL (Fin 2) (v.adicCompletion K), ∀ u₁ ∈ U, ∀ u₂ ∈ U, fv (u₁ * g * u₂) = fv g := by sorry
