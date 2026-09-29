-- Prove2me | Theorems.Thm_AutomorphicForm_integral_mul_eq_integral_mul_of_forall_integral_subgroup_mul_eq_one
-- name    : AutomorphicForm.integral_mul_eq_integral_mul_of_forall_integral_subgroup_mul_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/2f417e8e-c56c-52aa-9a10-4d307fc15576
-- title:
--   Independence of the weighted integral from the section weight
-- statement:
--   Let $G$ be a group equipped with a measurable space structure for which multiplication is measurable as a function of the pair of arguments, and let $\mu$ be an $s$-finite, left-invariant measure on $G$. Let $T$ be a subgroup of $G$, itself equipped with a measurable space structure for which inversion is measurable and for which the inclusion $T \to G$, $t \mapsto t$, is measurable, and let $\tau$ be an $s$-finite measure on $T$ invariant under inversion. Let $F : G \to \mathbb{C}$ be measurable and left $T$-invariant, i.e. $F(tx) = F(x)$ for all $t \in T$ and $x \in G$. Let $w, w' : G \to \mathbb{R}$ be measurable and pointwise non-negative, and suppose that for every $x$ with $F(x) \neq 0$ one has $\int_T w(tx)\,d\tau(t) = 1$ and likewise $\int_T w'(tx)\,d\tau(t) = 1$; that is, both weights have total mass $1$ on each coset $Tx$ meeting the support of $F$. Then $$\int_G F(x)\,w(x)\,d\mu(x) = \int_G F(x)\,w'(x)\,d\mu(x),$$ the real-valued weights being coerced to $\mathbb{C}$. No integrability hypotheses are imposed: the integrals are Bochner integrals, taking the value $0$ where the integrand fails to be integrable.
--
--   This is the uniqueness, or section-independence, statement for weighted integrals of a $T$-invariant function: any two weights normalising to $1$ on the relevant cosets of $T$ compute the same integral over $G$, which is the integral of $F$ over $T \backslash G$ in disguise. It is used in the construction and comparison of local and archimedean test functions for automorphic forms, where choices of such weights enter the matching conditions and the splitting of Hecke operators at a prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integral_mul_eq_integral_mul_of_forall_integral_subgroup_mul_eq_one.lean

import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem AutomorphicForm.integral_mul_eq_integral_mul_of_forall_integral_subgroup_mul_eq_one
    {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant]
    (T : Subgroup G) [MeasurableSpace T] [MeasurableInv T]
    (hT : Measurable (Subtype.val : T → G))
    (τ : Measure T) [SFinite τ] [τ.IsInvInvariant]
    (F : G → ℂ) (hF : Measurable F) (hFT : ∀ (t : T) (x : G), F ((t : G) * x) = F x)
    (w w' : G → ℝ) (hw : ∀ x, 0 ≤ w x) (hw' : ∀ x, 0 ≤ w' x)
    (hwm : Measurable w) (hw'm : Measurable w')
    (h1 : ∀ x, F x ≠ 0 → ∫ t : T, w ((t : G) * x) ∂τ = 1)
    (h1' : ∀ x, F x ≠ 0 → ∫ t : T, w' ((t : G) * x) ∂τ = 1) :
    ∫ x, F x * (w x : ℂ) ∂μ = ∫ x, F x * (w' x : ℂ) ∂μ := by sorry
