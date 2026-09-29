-- Prove2me | Theorems.Thm_FiniteField_exists_forall_affineMap_ne_zero
-- name    : FiniteField.exists_forall_affineMap_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/d73da8f7-bf09-56d6-b2dd-942592bc541d
-- title:
--   Fewer than q affine conditions on 𝔽ⁿ are simultaneously avoidable
-- statement:
--   Let $\mathbb{F}$ be a finite field, let $n$ be a natural number, let $\iota$ be a finite index type, and for each $j \in \iota$ let $V_j$ be an $\mathbb{F}$-vector space. Given a family $\varphi$ assigning to each $j$ an affine map $\varphi_j \colon \mathbb{F}^n \to V_j$ over $\mathbb{F}$ (the source being the space of functions $\mathrm{Fin}\,n \to \mathbb{F}$), suppose that no $\varphi_j$ vanishes identically, i.e. for each $j$ there exists some $x$ with $\varphi_j(x) \neq 0$, and suppose that the number of indices is smaller than the number of elements of $\mathbb{F}$, $\#\iota < \#\mathbb{F}$. The conclusion is that a single point works for all conditions at once: there exists $x \in \mathbb{F}^n$ such that $\varphi_j(x) \neq 0$ for every $j \in \iota$. Note that $n = 0$ is permitted, in which case the unique point of $\mathbb{F}^0$ is the required one, and $\iota$ may be empty.
--
--   An elementary counting statement about finite fields: the zero loci of finitely many nonzero affine maps on $\mathbb{F}^n$ cannot cover $\mathbb{F}^n$ as soon as there are fewer of them than there are elements of $\mathbb{F}$. It is used to choose a point of an affine space over a finite field avoiding a short list of affine non-vanishing conditions, and is cited by [`FiniteField.exists_forall_affineMap_apply_ne_zero_of_forall_lt`](thm.html#FiniteField.exists_forall_affineMap_apply_ne_zero_of_forall_lt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FiniteField_exists_forall_affineMap_ne_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem FiniteField.exists_forall_affineMap_ne_zero
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] {n : ℕ} {ι : Type*} [Fintype ι]
    {V : ι → Type*} [∀ j, AddCommGroup (V j)] [∀ j, Module 𝔽 (V j)]
    (φ : ∀ j, (Fin n → 𝔽) →ᵃ[𝔽] V j) (hφ : ∀ j, ∃ x, φ j x ≠ 0)
    (hm : Fintype.card ι < Fintype.card 𝔽) :
    ∃ x, ∀ j, φ j x ≠ 0 := by sorry
