-- Prove2me | Theorems.Thm_AutomorphicForm_eq_ite_inv_norm_sub_one_of_isOrbitalIntegral_indicator_localIntegralSet_diagonal
-- name    : AutomorphicForm.eq_ite_inv_norm_sub_one_of_isOrbitalIntegral_indicator_localIntegralSet_diagonal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/96852711-80ce-5d93-9180-dea04b456353
-- title:
--   Unit orbital integral at the split class diag(au,a)
-- statement:
--   Let $K$ be a number field, $v$ a height-one prime of the ring of integers $\mathcal O_K$, and $K_v$ the associated adic completion, with valuation ring $\mathcal O_v$. Let $a,u \in K_v$ with $u \neq 1$, and let $t \in \mathrm{GL}_2(K_v)$ be an element whose underlying matrix is the diagonal matrix with entries $au$ and $a$. Write $S =$ [`AutomorphicForm.localIntegralSet K v`](def/AutomorphicForm_LocalOrbitalBase.html#L100) for the set of $g \in \mathrm{GL}_2(K_v)$ such that the matrix of $g$ and the matrix of $g^{-1}$ both lie in `integralMatrixSet` of $\mathcal O_v$. Let $\tau$ be a Haar measure, for the Borel $\sigma$-algebra, on the centraliser subgroup $Z(t) =$ `Subgroup.centralizer {t}` in $\mathrm{GL}_2(K_v)$, normalised so that the preimage of $S$ in $Z(t)$ has $\tau$-mass $1$. Let $I \in \mathbb{C}$ be an orbital integral at $t$ with respect to $\tau$ of the indicator function of $S$ with value $1$; that is, there is a nonnegative measurable compactly supported $w : \mathrm{GL}_2(K_v) \to \mathbb{R}$ with $\int_{Z(t)} w(sx)\,d\tau(s) = 1$ for every $x$ with $x^{-1}tx \in S$, and $I = \int \mathbf 1_S(x^{-1}tx)\,w(x)\,d\mu(x)$, where $\mu$ is the Haar measure [`AutomorphicForm.localHaar K v`](def/AutomorphicForm_LocalOrbitalBase.html#L168) on $\mathrm{GL}_2(K_v)$ normalised by the compact set $S$. Then $I = \|u-1\|^{-1}$ if $\|a\| = 1$ and $\|u\| = 1$, and $I = 0$ otherwise.
--
--   This is the unramified local factor of a hyperbolic (split regular semisimple) orbital integral of the unit element of the local Hecke algebra: the conjugacy class of $\operatorname{diag}(au,a)$ meets $\mathrm{GL}_2(\mathcal O_v)$ only when both eigenvalues are units, and then the value is $\|u-1\|^{-1}$. It is obtained from the Iwasawa-unfolding formula for diagonal classes, [`AutomorphicForm.eq_norm_inv_mul_integral_localIntegralSet_integral_conj_unipotentGL2_of_isOrbitalIntegral_of_diagonal`](thm.html#AutomorphicForm.eq_norm_inv_mul_integral_localIntegralSet_integral_conj_unipotentGL2_of_isOrbitalIntegral_of_diagonal), and feeds the computation of weighted global class integrals as Euler products over the finite places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_eq_ite_inv_norm_sub_one_of_isOrbitalIntegral_indicator_localIntegralSet_diagonal.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem AutomorphicForm.eq_ite_inv_norm_sub_one_of_isOrbitalIntegral_indicator_localIntegralSet_diagonal
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (a u : v.adicCompletion K) (hu1 : u ≠ 1)
    (t : GL (Fin 2) (v.adicCompletion K))
    (ht : (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = Matrix.diagonal ![a * u, a])
    (τ : @Measure (AutomorphicForm.localCentralizer K v t) (AutomorphicForm.localCentralizerBorel K v t))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v t) τ)
    (hτ1 : τ (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (I : ℂ)
    (hI : AutomorphicForm.IsOrbitalIntegral K v t τ
      ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)) I) :
    I = if ‖a‖ = 1 ∧ ‖u‖ = 1 then (((‖u - 1‖ : ℝ) : ℂ))⁻¹ else 0 := by sorry
