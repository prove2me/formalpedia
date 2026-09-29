-- Prove2me | Theorems.Thm_AutomorphicForm_measure_setOf_integral_valuation_det_eq_geom_sum_absNorm_mul_measure_localIntegralSet
-- name    : AutomorphicForm.measure_setOf_integral_valuation_det_eq_geom_sum_absNorm_mul_measure_localIntegralSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/adaf6fc1-2945-5505-9d0e-224565012a5e
-- title:
--   Volume of integral matrices of determinant valuation k
-- statement:
--   Let $K$ be a number field and let $v$ be a height-one prime of the ring of integers $\mathcal{O}_K$, with $v$-adic completion $K_v =$ `v.adicCompletion K` and valuation ring $\mathcal{O}_v =$ `v.adicCompletionIntegers K`. Equip the group $\mathrm{GL}_2(K_v)$ with the Borel $\sigma$-algebra of its topology ([`AutomorphicForm.localGLBorel`](def/AutomorphicForm_LocalOrbitalBase.html#L154)), let $\mu$ be a measure on this measurable space, assumed invariant under left translations, and let $k$ be a natural number. The assertion is an equality in $[0,\infty]$: the $\mu$-measure of the set of those $g \in \mathrm{GL}_2(K_v)$ such that every entry $g_{ij}$ of the underlying matrix lies in $\mathcal{O}_v$ and the valuation of $\det g$ (the unit $\det g$ viewed in $K_v$, measured by `Valued.v`) equals $\exp(-k)$ in $\mathbb{Z}^{\mathrm{mult}} \cup \{0\}$, i.e. $\det g$ has valuation exactly $k$ in additive normalisation, is equal to $\bigl(\sum_{i=0}^{k} q^{i}\bigr) \cdot \mu(\mathrm{GL}_2(\mathcal{O}_v))$, where $q$ is the absolute norm `Ideal.absNorm v.asIdeal` of the prime, coerced into $[0,\infty]$, and $\mathrm{GL}_2(\mathcal{O}_v)$ is [`AutomorphicForm.localIntegralSet K v`](def/AutomorphicForm_LocalOrbitalBase.html#L100), the set of $g \in \mathrm{GL}_2(K_v)$ whose matrix and whose inverse matrix both lie in `integralMatrixSet` of $\mathcal{O}_v$. No finiteness, regularity or non-triviality hypothesis is placed on $\mu$.
--
--   This is the measure-theoretic form of the classical count of the integral $2\times 2$ matrices of determinant of valuation $k$ modulo the maximal compact subgroup $\mathrm{GL}_2(\mathcal{O}_v)$, equivalently of the $\mathcal{O}_v$-lattices of index $q^k$ in $\mathcal{O}_v^2$; the factor $1 + q + \cdots + q^k$ is the degree of the Hecke operator at $v$ for the $k$-th power of the prime. It is used in the local analysis of integrals over $\mathrm{GL}_2(K_v)$, notably by [`AutomorphicForm.setLIntegral_nnnorm_det_rpow_setOf_integral_eq_measure_localIntegralSet_mul`](thm.html#AutomorphicForm.setLIntegral_nnnorm_det_rpow_setOf_integral_eq_measure_localIntegralSet_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_measure_setOf_integral_valuation_det_eq_geom_sum_absNorm_mul_measure_localIntegralSet.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem AutomorphicForm.measure_setOf_integral_valuation_det_eq_geom_sum_absNorm_mul_measure_localIntegralSet
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (μ : @Measure (GL (Fin 2) (v.adicCompletion K)) (AutomorphicForm.localGLBorel K v))
    (hμ : @Measure.IsMulLeftInvariant (GL (Fin 2) (v.adicCompletion K))
      (AutomorphicForm.localGLBorel K v) _ μ)
    (k : ℕ) :
    μ {g : GL (Fin 2) (v.adicCompletion K) |
        (∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K) ∧
          Valued.v ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
            WithZero.exp (-(k : ℤ))} =
      (∑ i ∈ Finset.range (k + 1), ((Ideal.absNorm v.asIdeal : ℕ) : ENNReal) ^ i) *
        μ (AutomorphicForm.localIntegralSet K v) := by sorry
