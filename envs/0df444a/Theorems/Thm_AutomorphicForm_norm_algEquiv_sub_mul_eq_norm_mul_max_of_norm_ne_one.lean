-- Prove2me | Theorems.Thm_AutomorphicForm_norm_algEquiv_sub_mul_eq_norm_mul_max_of_norm_ne_one
-- name    : AutomorphicForm.norm_algEquiv_sub_mul_eq_norm_mul_max_of_norm_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/2e9734d5-a228-51e1-89e4-049811723e85
-- title:
--   Norm of a twisted difference θ y - cy when ‖c‖ ≠ 1
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $v$ be a height-one prime of the ring of integers $\mathcal{O}_K$, and let $w$ be an extension of $v$ to $\mathcal{O}_L$, that is, a pair consisting of a height-one prime of $\mathcal{O}_L$ together with the requirement that its contraction along $\mathcal{O}_K \to \mathcal{O}_L$ equals $v$; write $K_v$ and $L_w$ for the associated adic completions, each with its valuation norm. Let $\theta$ be a $K_v$-algebra automorphism of $L_w$, and let $c \in L_w$ satisfy $\|c\| \neq 1$. Then for every $y \in L_w$,
--   $$\|\theta(y) - c\,y\| = \|y\|\cdot\max\bigl(1, \|c\|\bigr).$$
--   No separability, normality or ramification hypothesis on $L/K$ is imposed, and $\theta$ is an arbitrary automorphism of $L_w$ over $K_v$; the conclusion holds for all $y$, including $y = 0$, where both sides vanish.
--
--   This is the ultrametric computation underlying the "unequal valuations" case of a twisted local integral: if the multiplier $c$ has norm different from $1$, the norm of the twisted difference $\theta(y) - cy$ is determined exactly, with no cancellation. It is used in the evaluation of twisted conjugation integrals and Hecke-word contributions in [`AutomorphicForm.integral_heckeWord_twistedConj_mul_weight_eq_two_mul_log_mul_twistedShellValue`](thm.html#AutomorphicForm.integral_heckeWord_twistedConj_mul_weight_eq_two_mul_log_mul_twistedShellValue) and [`AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_finrank`](thm.html#AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_finrank).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_norm_algEquiv_sub_mul_eq_norm_mul_max_of_norm_ne_one.lean

import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_LocalOrbitalBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem AutomorphicForm.norm_algEquiv_sub_mul_eq_norm_mul_max_of_norm_ne_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (c : w.1.adicCompletion L) (hc : ‖c‖ ≠ 1) (y : w.1.adicCompletion L) :
    ‖θ y - c * y‖ = ‖y‖ * max 1 ‖c‖ := by sorry
