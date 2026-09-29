-- Prove2me | Theorems.Thm_AutomorphicForm_measureReal_norm_eq_and_norm_algEquiv_sub_mul_eq_of_prod_eq_of_ramificationIdx_eq_one
-- name    : AutomorphicForm.measureReal_norm_eq_and_norm_algEquiv_sub_mul_eq_of_prod_eq_of_ramificationIdx_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/d6eb1333-6b69-5691-8601-7557c50eff60
-- title:
--   Shell measures for the twisted difference θ y - cy
-- statement:
--   Let $K \subseteq L$ be number fields, $v$ a nonzero prime of $\mathcal O_K$ and $w$ an element of $v$'s extension set, i.e. a nonzero prime of $\mathcal O_L$ whose contraction to $\mathcal O_K$ is $v$; write $q =$ `Ideal.absNorm v.asIdeal`, $N(w) =$ `Ideal.absNorm w.1.asIdeal` and $\ell = \operatorname{finrank}_{K_v} L_w$ for the completions. Assume the ramification index `Ideal.ramificationIdx'` of $w$ over its contraction is $1$, that $\ell$ is prime, and let $\theta$ be a $K_v$-algebra automorphism of $L_w$ of order $\ell$ for which some $y$ has $\|y\| \le 1$ and $\|\theta y - y\| = 1$. Let $c \in L_w$, $n \in K_v$ with $\|n\| = 1$, $d \in \mathbb N$ with $\|1-n\| = q^{-d}$, and $\prod_{i<\ell} \theta^i(c) = n$ in $L_w$. Let $P : \mathbb N \to \mathbb R$ satisfy $P(0)=1$, $P(i) = \bigl(q^{(\ell-1)(i-1)}\sum_{t<\ell} q^t\bigr)^{-1}$ for $1 \le i \le d$, and $P(i)=0$ for $i>d$. Let $\mu_E$ be an additive Haar measure on $L_w$ (with its Borel structure) normalised by $\mu_E(\mathcal O_w) = 1$, and let $m \ge 1$. Then: (i) every $y$ with $\|y\| = N(w)^m$ satisfies $\|\theta y - cy\| = N(w)^{m-t}$ for some $t \le d$; (ii) for $i \le d$ with $i < m$, the measure of $\{y : \|y\| = N(w)^m,\ \|\theta y - cy\| = N(w)^{m-i}\}$ is $(N(w)^m - N(w)^{m-1})(P(i) - P(i+1))$; (iii) the measure of $\{y : \|y\| = N(w)^m,\ \|\theta y - cy\| \le 1\}$ is $(N(w)^m - N(w)^{m-1})\,P(m)$ (measures read as real numbers).
--
--   This is the local shell computation at an unramified place occurring in Langlands' analysis of twisted orbital integrals for base change in prime degree: the $K_v$-linear operator $y \mapsto \theta y - cy$ is measured on each norm shell of $L_w$. It is used in the evaluation of the twisted Hecke integrals, namely by [`AutomorphicForm.integral_heckeWord_twistedConj_mul_weight_eq_two_mul_log_mul_twistedShellValue`](thm.html#AutomorphicForm.integral_heckeWord_twistedConj_mul_weight_eq_two_mul_log_mul_twistedShellValue) and [`AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_finrank`](thm.html#AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_finrank).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_measureReal_norm_eq_and_norm_algEquiv_sub_mul_eq_of_prod_eq_of_ramificationIdx_eq_one.lean

import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_LocalOrbitalBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem AutomorphicForm.measureReal_norm_eq_and_norm_algEquiv_sub_mul_eq_of_prod_eq_of_ramificationIdx_eq_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (hprime : (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)).Prime)
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hθ : orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))
    (hres : ∃ y : w.1.adicCompletion L, ‖y‖ ≤ 1 ∧ ‖θ y - y‖ = 1)
    (c : w.1.adicCompletion L) (n : v.adicCompletion K) (hn : ‖n‖ = 1) (d : ℕ)
    (hd : ‖1 - n‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(d : ℤ)))
    (hc : ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)), (θ ^ i) c =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) n)

    (P : ℕ → ℝ) (hP0 : P 0 = 1)
    (hP : ∀ i : ℕ, 1 ≤ i → i ≤ d →
      P i = ((Ideal.absNorm v.asIdeal : ℝ) ^
          ((Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) - 1) * (i - 1)) *
        ∑ t ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
          (Ideal.absNorm v.asIdeal : ℝ) ^ t)⁻¹)
    (hPd : ∀ i : ℕ, d < i → P i = 0)

    [MeasurableSpace (w.1.adicCompletion L)] [BorelSpace (w.1.adicCompletion L)]
    (μE : Measure (w.1.adicCompletion L)) [μE.IsAddHaarMeasure]
    (hμE : μE (w.1.adicCompletionIntegers L : Set (w.1.adicCompletion L)) = 1)
    (m : ℕ) (hm : 1 ≤ m) :
    (∀ y : w.1.adicCompletion L, ‖y‖ = (Ideal.absNorm w.1.asIdeal : ℝ) ^ m →
        ∃ t : ℕ, t ≤ d ∧ ‖θ y - c * y‖ = (Ideal.absNorm w.1.asIdeal : ℝ) ^ ((m : ℤ) - t)) ∧
    (∀ i : ℕ, i ≤ d → i < m →
        (μE {y : w.1.adicCompletion L | ‖y‖ = (Ideal.absNorm w.1.asIdeal : ℝ) ^ m ∧
            ‖θ y - c * y‖ = (Ideal.absNorm w.1.asIdeal : ℝ) ^ (m - i)}).toReal =
          ((Ideal.absNorm w.1.asIdeal : ℝ) ^ m - (Ideal.absNorm w.1.asIdeal : ℝ) ^ (m - 1)) *
            (P i - P (i + 1))) ∧
    (μE {y : w.1.adicCompletion L | ‖y‖ = (Ideal.absNorm w.1.asIdeal : ℝ) ^ m ∧ ‖θ y - c * y‖ ≤ 1}).toReal =
      ((Ideal.absNorm w.1.asIdeal : ℝ) ^ m - (Ideal.absNorm w.1.asIdeal : ℝ) ^ (m - 1)) * P m := by sorry
