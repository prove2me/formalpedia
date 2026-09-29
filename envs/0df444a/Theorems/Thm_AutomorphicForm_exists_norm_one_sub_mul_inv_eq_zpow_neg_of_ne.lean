-- Prove2me | Theorems.Thm_AutomorphicForm_exists_norm_one_sub_mul_inv_eq_zpow_neg_of_ne
-- name    : AutomorphicForm.exists_norm_one_sub_mul_inv_eq_zpow_neg_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/8ae09434-28c8-5dd0-b809-41ec2769c7bc
-- title:
--   Norm of 1-ba⁻¹ is a power of N(v)⁻¹
-- statement:
--   Let $K$ be a number field and let $v$ be a point of the height-one spectrum of the ring of integers $\mathcal{O}_K$, that is, a nonzero prime ideal of $\mathcal{O}_K$; let $K_v$ denote the $v$-adic completion `v.adicCompletion K`, equipped with its Mathlib norm. Let $a$ and $b$ be units of $K_v$, assumed distinct as units. The assertion is that there exists a natural number $d$ with the following property: if the norms of the images of $a$ and $b$ in $K_v$ coincide, $\|a\| = \|b\|$, then the norm of $1 - ba^{-1}$, where the inverse and the product are formed in the unit group $K_v^{\times}$ and the result is coerced into $K_v$, equals $(\mathrm{absNorm}\,v.\mathrm{asIdeal})^{-d}$, the $(-d)$-th integer power of the real number given by the absolute norm of the prime ideal $v$. Note the order of the quantifiers: $d$ is produced before, and may depend on, the equality of norms, so when $\|a\| \neq \|b\|$ the implication is vacuous and any $d$ (for instance $d = 0$) witnesses the conclusion.
--
--   This is the elementary local fact that a unit ratio $ba^{-1} \neq 1$ of equal-norm elements satisfies $\|1 - ba^{-1}\| = N(v)^{-d}$ for some $d \geq 0$, the norm on a $v$-adic completion taking values in the powers of $N(v)$. It supplies the exponent $d$ used in [`AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_finrank`](thm.html#AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_finrank).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_norm_one_sub_mul_inv_eq_zpow_neg_of_ne.lean

import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_LocalOrbitalBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem AutomorphicForm.exists_norm_one_sub_mul_inv_eq_zpow_neg_of_ne
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b) :
    ∃ d : ℕ, ‖(a : v.adicCompletion K)‖ = ‖(b : v.adicCompletion K)‖ →
      ‖1 - ((b * a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(d : ℤ)) := by sorry
