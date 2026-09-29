-- Prove2me | Theorems.Thm_AutomorphicForm_eq_ite_sum_of_isWeightedOrbitalIntegral_indicator_localIntegralSet_diagUnits2
-- name    : AutomorphicForm.eq_ite_sum_of_isWeightedOrbitalIntegral_indicator_localIntegralSet_diagUnits2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/6ebf0c01-96f4-5523-94fb-1d6df75fe9d9
-- title:
--   Weighted orbital integral of the spherical unit at diag(a,b)
-- statement:
--   Let $K$ be a number field, $v$ a nonzero prime of $\mathcal O_K$ with completion $K_v$ and residue cardinality $q = \mathrm{absNorm}(v)$, and let $a \neq b$ be units of $K_v$; let $m \in \mathbb Z$ satisfy $\|a - b\| = q^{-m}$. Put $\gamma = \mathrm{diag}(a,b) \in \mathrm{GL}_2(K_v)$, the invertible matrix `diagUnits2 a b` with inverse $\mathrm{diag}(a^{-1},b^{-1})$, and let $\tau$ be a Haar measure for the Borel structure on the centraliser of $\{\gamma\}$ in $\mathrm{GL}_2(K_v)$ which assigns mass $1$ to the set of centralising elements $t$ lying in `localIntegralSet K v`, i.e. such that both $t$ and $t^{-1}$ have all entries in the valuation ring of $K_v$. Let $J \in \mathbb C$ be a weighted orbital integral of the $\mathbb C$-valued indicator function $f$ of `localIntegralSet K v` at $\gamma$ with respect to $\tau$: that is, there is a real-valued $s$ on $\mathrm{GL}_2(K_v)$ satisfying the section-function predicate `IsSectionFnOn` for $\gamma$, $\tau$ and $f$ with $J = \int f(x^{-1}\gamma x)\, W(x)\, s(x)\, d\mu(x)$, where $\mu$ is the Haar measure `localHaar K v` of $\mathrm{GL}_2(K_v)$ normalised on the integral compact set and $W(x) = 2\log\bigl(\max(\|x_{00}\|,\|x_{01}\|)\cdot \mathrm{rowMaxNorm}(x)/\|\det x\|\bigr)$. Then $J = 0$ unless $\|a\| = \|b\| = 1$, in which case $J$ is the real number $2\log q \cdot \sum_{s=0}^{\max(m,0)} s\,(q^{s} - q^{s}/q)$, viewed in $\mathbb C$.
--
--   This is the untwisted half of the weighted fundamental lemma for the unit element of the local spherical Hecke algebra of $\mathrm{GL}_2$ at a split regular semisimple element, evaluated in closed form in terms of the separation $q^{-m}$ of the two eigenvalues. It feeds the comparison of twisted and untwisted weighted orbital integrals, being cited by [`AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_indicator_of_unramified`](thm.html#AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_indicator_of_unramified) and by the semilocal twisted statement for nontrivial extensions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_eq_ite_sum_of_isWeightedOrbitalIntegral_indicator_localIntegralSet_diagUnits2.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.eq_ite_sum_of_isWeightedOrbitalIntegral_indicator_localIntegralSet_diagUnits2
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b) (m : ℤ)
    (hm : ‖(a : v.adicCompletion K) - b‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-m))
    (τ : @Measure (AutomorphicForm.localCentralizer K v (diagUnits2 a b))
      (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)) τ)
    (hτ1 : τ {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v} = 1)
    (J : ℂ)
    (hJ : AutomorphicForm.IsWeightedOrbitalIntegral K v (diagUnits2 a b) τ
      ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)) J) :
    J = if ‖(a : v.adicCompletion K)‖ = 1 ∧ ‖(b : v.adicCompletion K)‖ = 1 then
        (((2 * Real.log (Ideal.absNorm v.asIdeal) *
            ∑ s ∈ Finset.range (m.toNat + 1),
              (s : ℝ) * ((Ideal.absNorm v.asIdeal : ℝ) ^ s -
                (Ideal.absNorm v.asIdeal : ℝ) ^ s / (Ideal.absNorm v.asIdeal : ℝ)) : ℝ) : ℂ))
      else 0 := by sorry
