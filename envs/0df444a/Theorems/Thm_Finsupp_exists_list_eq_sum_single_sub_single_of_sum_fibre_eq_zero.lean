-- Prove2me | Theorems.Thm_Finsupp_exists_list_eq_sum_single_sub_single_of_sum_fibre_eq_zero
-- name    : Finsupp.exists_list_eq_sum_single_sub_single_of_sum_fibre_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/9967068a-793a-5d03-89e2-38f6e2136ce0
-- title:
--   Fibrewise zero-sum finitely supported ℤ-functions split into same-fibre differences
-- statement:
--   Let $\alpha$ and $\beta$ be types with decidable equality on $\beta$, let $\ell \colon \alpha \to \beta$ be any map, and let $D \colon \alpha \to_{\mathrm{f}} \mathbb{Z}$ be a finitely supported function. Assume that for every $b \in \beta$ the sum of $D(a)$ over those $a$ in the support of $D$ with $\ell(a) = b$ vanishes. Then there is a list $l$ of pairs $(p_1, p_2) \in \alpha \times \alpha$ such that every pair $p$ occurring in $l$ satisfies $\ell(p_1) = \ell(p_2)$, both $p_1$ and $p_2$ lie in the support of $D$, and $p_1 \neq p_2$; and such that $D$ equals the sum of the finitely supported functions $\mathrm{single}(p_1, 1) - \mathrm{single}(p_2, 1)$ as $p$ ranges over $l$ (that is, the sum of the list obtained by mapping this function over $l$). Note that the list is a list, not a set: repetitions are permitted, and the membership conditions constrain only the entries of $D$'s support that actually occur.
--
--   An elementary splitting lemma: a finitely supported integer-valued function whose sum along each fibre of a map $\ell$ vanishes is a sum of differences $[a] - [a']$ of pairs of distinct points lying in a common fibre and in the support. It is used in [`AlgebraicCurve.exists_ne_zero_ord_eq_of_depthMass_eq_zero_of_semistableCovering_of_rankOne`](thm.html#AlgebraicCurve.exists_ne_zero_ord_eq_of_depthMass_eq_zero_of_semistableCovering_of_rankOne) to reduce a divisor with vanishing fibrewise mass to the case of a single difference of two points in one fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Finsupp_exists_list_eq_sum_single_sub_single_of_sum_fibre_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Finsupp.exists_list_eq_sum_single_sub_single_of_sum_fibre_eq_zero
    {α β : Type*} [DecidableEq β] (ℓ : α → β) (D : α →₀ ℤ)
    (hD : ∀ b : β, ((D.support.filter fun a => ℓ a = b).sum fun a => D a) = 0) :
    ∃ l : List (α × α), (∀ p ∈ l, ℓ p.1 = ℓ p.2 ∧ p.1 ∈ D.support ∧ p.2 ∈ D.support ∧ p.1 ≠ p.2) ∧
      D = (l.map fun p => (Finsupp.single p.1 1 - Finsupp.single p.2 1 : α →₀ ℤ)).sum := by sorry
