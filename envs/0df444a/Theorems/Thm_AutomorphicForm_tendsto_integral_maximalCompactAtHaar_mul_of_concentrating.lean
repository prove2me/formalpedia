-- Prove2me | Theorems.Thm_AutomorphicForm_tendsto_integral_maximalCompactAtHaar_mul_of_concentrating
-- name    : AutomorphicForm.tendsto_integral_maximalCompactAtHaar_mul_of_concentrating
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/c58244d0-53ad-526e-b459-8d88b539f5c0
-- title:
--   Pointwise convergence of averages against concentrating kernels
-- statement:
--   Let $K$ be a number field and let $\mathcal K =$ `maximalCompactAt K ∅` be the subgroup of $\mathrm{GL}_2(\mathbb A_K)$ consisting of those $k$ whose finite part lies in `finiteIntegralGL2` and whose component at each infinite place of $K$ is a row isometry, and whose component at *every* finite place is trivial (the index set $\emptyset^{c}$ being all of the height-one spectrum of $\mathcal O_K$); it carries the Haar measure `maximalCompactAtHaar K ∅` normalised to give the whole group mass $1$. Let $\kappa : \mathbb N \to \mathcal K \to \mathbb R$ be a sequence of functions such that each $\kappa_n$ is continuous, non-negative, has integral $1$ against this Haar measure, and is concentrating at the identity in the sense that for every neighbourhood $U$ of $1$ in $\mathcal K$ one has $\int_{U^{c}} \kappa_n \to 0$ as $n \to \infty$. Then for every continuous $f : \mathrm{GL}_2(\mathbb A_K) \to \mathbb C$ (the adelic group being given its Borel structure) and every $x \in \mathrm{GL}_2(\mathbb A_K)$, $\int_{\mathcal K} \kappa_n(k)\, f(xk)\,dk \to f(x)$ as $n \to \infty$.
--
--   This is the standard approximate-identity statement on a compact group, here for the archimedean maximal compact subgroup of $\mathrm{GL}_2(\mathbb A_K)$ acting by right translation on continuous functions. It supplies the pointwise-convergence clause used in [`AutomorphicForm.exists_isArchKFinite_tendsto_and_setLIntegral_le_of_mem_isotypicCuspSubmodule`](thm.html#AutomorphicForm.exists_isArchKFinite_tendsto_and_setLIntegral_le_of_mem_isotypicCuspSubmodule), where cusp forms are approximated by $\mathcal K$-finite vectors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_tendsto_integral_maximalCompactAtHaar_mul_of_concentrating.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.tendsto_integral_maximalCompactAtHaar_mul_of_concentrating
    (K : Type) [Field K] [NumberField K]
    (κ : ℕ → ↥(maximalCompactAt K ∅) → ℝ)
    (hκc : ∀ n, Continuous (κ n)) (hκ0 : ∀ n k, 0 ≤ κ n k) (hκ1 : ∀ n, ∫ k, κ n k ∂(maximalCompactAtHaar K ∅) = 1)
    (hκU : ∀ U ∈ nhds (1 : ↥(maximalCompactAt K ∅)),
      Filter.Tendsto (fun n => ∫ k in Uᶜ, κ n k ∂(maximalCompactAtHaar K ∅)) Filter.atTop (nhds 0))
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (x : AdelicGL2 (𝓞 K) K) :
    Filter.Tendsto (fun n => ∫ k, (κ n k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactAtHaar K ∅)) Filter.atTop
      (nhds (f x)) := by sorry
