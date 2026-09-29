-- Prove2me | Theorems.Thm_AutomorphicForm_localHaar_setOf_unipotentGL2_mul_eq_relIndex_and_setIntegral_weight_eq_of_norm_eq_inv
-- name    : AutomorphicForm.localHaar_setOf_unipotentGL2_mul_eq_relIndex_and_setIntegral_weight_eq_of_norm_eq_inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/93d29941-adb1-5309-ac78-79380e65e308
-- title:
--   Haar volume and weighted integral of horocycle shells in GL₂(Kᵥ)
-- statement:
--   Let $K$ be a number field, $v$ a nonzero prime of its ring of integers, $K_v$ the $v$-adic completion and $\mathcal O_v \subseteq K_v$ its valuation ring. Let $\Lambda$ be an additive subgroup of $K_v$ and $\varpi \in K_v$ an element with $\|\varpi\| = (\mathrm{N}v)^{-1}$, where $\mathrm{N}v$ is the absolute norm of $v$; let $m$ be a natural number. For $s \in \mathbb N$ write $\Lambda_s = \Lambda \cap \{y : \varpi^s y \in \mathcal O_v\}$ and $i_s = [\Lambda_s : \Lambda_s \cap \mathcal O_v]$ (the relative index of the additive subgroup $\mathcal O_v$ with respect to $\Lambda_s$), and assume $i_s \neq 0$ for all $s \le m$. Put $n(y) = \begin{pmatrix} 1 & y \\ 0 & 1\end{pmatrix}$ and $V_s = \{\, n(y)k : y \in \Lambda_s,\ k \in \mathrm{localIntegralSet}\,\}$, where `localIntegralSet` consists of those $k \in \mathrm{GL}_2(K_v)$ for which both $k$ and $k^{-1}$ lie in `integralMatrixSet` over $\mathcal O_v$; let $\mu$ be the Haar measure on $\mathrm{GL}_2(K_v)$ (with its Borel structure) normalised so that this set has measure $1$. Then: (i) $\mu(V_s) = i_s$ for every $s \le m$ (the natural number cast into $[0,\infty]$); and (ii) with $w(x) = 2\log\bigl(\max(\|x_{00}\|,\|x_{01}\|)\max(\|x_{10}\|,\|x_{11}\|)/\|\det x\|\bigr)$, $$\int_{V_m} w \, d\mu = 2\log(\mathrm{N}v) \sum_{s=0}^{m-1} (s+1)\,(i_{s+1} - i_s).$$
--
--   This is the standard non-archimedean computation for the horocycle shells $n(\Lambda_s)\mathrm{GL}_2(\mathcal O_v)$: their Haar volume counts the cosets of $\Lambda_s \cap \mathcal O_v$ in $\Lambda_s$, and the local weight is constant equal to $2(s+1)\log \mathrm{N}v$ on $V_{s+1} \setminus V_s$. It feeds the local orbital and weighted-orbital integrals over $\mathrm{GL}_2(K_v)$ used later, in particular the evaluations of integrals of indicators of the integral set against twisted conjugation and against the local weight, and the construction of torus sections with prescribed norm data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_localHaar_setOf_unipotentGL2_mul_eq_relIndex_and_setIntegral_weight_eq_of_norm_eq_inv.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem AutomorphicForm.localHaar_setOf_unipotentGL2_mul_eq_relIndex_and_setIntegral_weight_eq_of_norm_eq_inv
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (Λ : AddSubgroup (v.adicCompletion K)) (ϖ : v.adicCompletion K)
    (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹) (m : ℕ)
    (hfin : ∀ s ≤ m, (v.adicCompletionIntegers K).toAddSubgroup.relIndex
      (Λ ⊓ (v.adicCompletionIntegers K).toAddSubgroup.comap (AddMonoidHom.mulLeft (ϖ ^ s))) ≠ 0) :
    (∀ s ≤ m, AutomorphicForm.localHaar K v
        {x | ∃ (y : v.adicCompletion K) (k : GL (Fin 2) (v.adicCompletion K)),
          (y ∈ Λ ∧ ϖ ^ s * y ∈ v.adicCompletionIntegers K) ∧ k ∈ AutomorphicForm.localIntegralSet K v ∧
            x = AutomorphicForm.unipotentGL2 y * k} =
      (v.adicCompletionIntegers K).toAddSubgroup.relIndex
        (Λ ⊓ (v.adicCompletionIntegers K).toAddSubgroup.comap (AddMonoidHom.mulLeft (ϖ ^ s)))) ∧
    (∫ x in {x | ∃ (y : v.adicCompletion K) (k : GL (Fin 2) (v.adicCompletion K)),
          (y ∈ Λ ∧ ϖ ^ m * y ∈ v.adicCompletionIntegers K) ∧ k ∈ AutomorphicForm.localIntegralSet K v ∧
            x = AutomorphicForm.unipotentGL2 y * k},
        AutomorphicForm.LocalWeight.weight x ∂(AutomorphicForm.localHaar K v)) =
      2 * Real.log (Ideal.absNorm v.asIdeal) *
        ∑ s ∈ Finset.range m, ((s + 1 : ℕ) : ℝ) *
          (((v.adicCompletionIntegers K).toAddSubgroup.relIndex
              (Λ ⊓ (v.adicCompletionIntegers K).toAddSubgroup.comap (AddMonoidHom.mulLeft (ϖ ^ (s + 1)))) : ℝ) -
            ((v.adicCompletionIntegers K).toAddSubgroup.relIndex
              (Λ ⊓ (v.adicCompletionIntegers K).toAddSubgroup.comap (AddMonoidHom.mulLeft (ϖ ^ s))) : ℝ)) := by sorry
