-- Prove2me | Theorems.Thm_FiniteField_exists_forall_affineMap_apply_ne_zero_of_forall_lt
-- name    : FiniteField.exists_forall_affineMap_apply_ne_zero_of_forall_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/0039aa04-a01b-549c-9a0f-8fd2f12cdda6
-- title:
--   Row-by-row avoidance of affine conditions over a finite field
-- statement:
--   Let $\mathbb{F}$ be a finite field, let $s$ be a natural number and let $n : \mathrm{Fin}\,s \to \mathbb{N}$; for each $i < s$ let $\iota\,i$ be a finite index type and let $V\,i\,j$, for $j \in \iota\,i$, be $\mathbb{F}$-vector spaces (abelian groups with an $\mathbb{F}$-module structure). Write $X = \prod_{i' < s} (\mathrm{Fin}(n\,i') \to \mathbb{F})$ for the space of tuples of rows. The datum is a family $\varphi$ assigning to each $i < s$, each tuple $x \in X$ and each $j \in \iota\,i$ an affine map $\varphi\,i\,x\,j : (\mathrm{Fin}(n\,i) \to \mathbb{F}) \to V\,i\,j$ over $\mathbb{F}$. Three hypotheses are imposed: (i) for each $i$, the whole family $\varphi\,i\,x$ depends on $x$ only through the coordinates $x\,i'$ with $i' < i$, that is, $\varphi\,i\,x = \varphi\,i\,x'$ whenever $x\,i' = x'\,i'$ for all $i' < i$; (ii) no $\varphi\,i\,x\,j$ vanishes identically, i.e. for all $i$, $x$, $j$ there is $y$ with $\varphi\,i\,x\,j\,(y) \neq 0$; (iii) $\#(\iota\,i) < \#\mathbb{F}$ for every $i$. The conclusion is that there exists a tuple $x \in X$ such that $\varphi\,i\,x\,j\,(x\,i) \neq 0$ for all $i < s$ and all $j \in \iota\,i$, so that each row simultaneously satisfies its own, self-referential, family of non-vanishing conditions.
--
--   This is an elementary counting statement over finite fields: a triangular (row-by-row) version of the fact that fewer than $\#\mathbb{F}$ non-trivial affine conditions on $\mathbb{F}^n$ can be simultaneously avoided. It is used by [`Matrix.exists_bifiltered_unimodular_of_forall_block_avoidance`](thm.html#Matrix.exists_bifiltered_unimodular_of_forall_block_avoidance) to construct a matrix one row block at a time, each block chosen to avoid conditions determined by the blocks already fixed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FiniteField_exists_forall_affineMap_apply_ne_zero_of_forall_lt.lean

import Mathlib
import Theorems.Thm_FiniteField_exists_forall_affineMap_ne_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem FiniteField.exists_forall_affineMap_apply_ne_zero_of_forall_lt
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] {s : ℕ} {n : Fin s → ℕ}
    {ι : Fin s → Type*} [∀ i, Fintype (ι i)]
    {V : ∀ i, ι i → Type*} [∀ i j, AddCommGroup (V i j)] [∀ i j, Module 𝔽 (V i j)]
    (φ : ∀ i, (∀ i' : Fin s, Fin (n i') → 𝔽) → ∀ j : ι i, (Fin (n i) → 𝔽) →ᵃ[𝔽] V i j)
    (hdep : ∀ i (x x' : ∀ i' : Fin s, Fin (n i') → 𝔽), (∀ i', i' < i → x i' = x' i') → φ i x = φ i x')
    (hφ : ∀ i x j, ∃ y, φ i x j y ≠ 0)
    (hm : ∀ i, Fintype.card (ι i) < Fintype.card 𝔽) :
    ∃ x : ∀ i : Fin s, Fin (n i) → 𝔽, ∀ i j, φ i x j (x i) ≠ 0 := by sorry
