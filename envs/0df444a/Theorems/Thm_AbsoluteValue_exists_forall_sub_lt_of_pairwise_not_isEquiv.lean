-- Prove2me | Theorems.Thm_AbsoluteValue_exists_forall_sub_lt_of_pairwise_not_isEquiv
-- name    : AbsoluteValue.exists_forall_sub_lt_of_pairwise_not_isEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/090291bb-28b0-5cbe-be81-4046e3b25cd1
-- title:
--   Artin–Whaples weak approximation for inequivalent absolute values
-- statement:
--   Let $K$ be a field and $\iota$ a finite index type, and let $v : \iota \to \mathrm{AbsoluteValue}\ K\ \mathbb{R}$ be a family of real absolute values on $K$. Assume that each $v_i$ is nontrivial, i.e. satisfies `AbsoluteValue.IsNontrivial`, and that the family is pairwise inequivalent in the sense that for all $i \neq j$ the relation `(v i).IsEquiv (v j)` fails. Let $a : \iota \to K$ be an arbitrary family of target values and let $\varepsilon > 0$ be real. Then there exists a single element $x \in K$ such that $v_i(x - a_i) < \varepsilon$ holds simultaneously for every index $i$. Note that the conclusion is the existence of one approximating element for the given $\varepsilon$, not the topological density statement; the latter follows by letting $\varepsilon$ vary. The case of an empty index type is included, and no Archimedean or non-Archimedean restriction is placed on the $v_i$.
--
--   This is the Artin–Whaples weak (simultaneous) approximation theorem: the diagonal image of $K$ is dense in the product of the metric completions attached to finitely many nontrivial pairwise inequivalent absolute values. It is used here to obtain density of the diagonal map from a number field into a finite product of adic completions times a product of completions at infinite places, in [`NumberField.denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi`](thm.html#NumberField.denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AbsoluteValue_exists_forall_sub_lt_of_pairwise_not_isEquiv.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AbsoluteValue.exists_forall_sub_lt_of_pairwise_not_isEquiv {K : Type*} [Field K] {ι : Type*} [Finite ι]
    {v : ι → AbsoluteValue K ℝ} (hv : ∀ i, (v i).IsNontrivial) (hne : Pairwise fun i j => ¬(v i).IsEquiv (v j))
    (a : ι → K) {ε : ℝ} (hε : 0 < ε) : ∃ x : K, ∀ i, v i (x - a i) < ε := by sorry
