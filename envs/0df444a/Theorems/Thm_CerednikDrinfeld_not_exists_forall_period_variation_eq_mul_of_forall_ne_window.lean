-- Prove2me | Theorems.Thm_CerednikDrinfeld_not_exists_forall_period_variation_eq_mul_of_forall_ne_window
-- name    : CerednikDrinfeld.not_exists_forall_period_variation_eq_mul_of_forall_ne_window
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/1695ea9b-85d3-56bb-bc8e-6669c827f320
-- title:
--   Period variation is a multiple of x₀ only on window vectors
-- statement:
--   Let $p$ be a prime, $\kappa$ a field of characteristic $p$, $G$ an additive abelian group and $x_0 \colon G \to \kappa$ an additive homomorphism. Let $a_1, a_{10}, a_{11}, a_{20}, s, t, r \in \kappa$ with $a_1 \neq 0$. Assume the period identity $a_1^{p} x_0(g) = (a_1^{p} a_{10} + a_1 a_{11})\, x_0(g)^{p} + (a_1^{p+1} a_{20} - a_1 a_{10}^{p} a_{11})\, x_0(g)^{p^2}$ for all $g \in G$; assume there are $g_1, g_2 \in G$ such that every relation $c_1 \cdot x_0(g_1) + c_2 \cdot x_0(g_2) = 0$ with $c_1, c_2 \in \mathbb{Z}$ (integer scalar multiples in $\kappa$) forces $p \mid c_1$ and $p \mid c_2$; and assume that $(s,t,r)$ is not of the form $(c_1 a_1 - c_2 a_{10},\, -c_1 a_1^{p} - c_2 a_{11},\, -c_1 a_{10}^{p} - c_2 a_{20})$ for any $c_1, c_2 \in \kappa$. Then there is no $\mu \in \kappa$ with $(a_1^{p+1} r - a_1 a_{10}^{p} t)\, x_0(g)^{p^2} + (a_1^{p} s + a_1 t)\, x_0(g)^{p} = \mu\, x_0(g)$ for all $g \in G$.
--
--   This is the field-theoretic core of the non-degeneracy step for first-order variations of a $p$-adic period: under the period equation and $\mathbb{F}_p$-independence of two values of $x_0$, the variation $(s,t,r)$ can make the associated additive expression proportional to $x_0$ only if it lies in the two-dimensional 'window' spanned by $(a_1, -a_1^{p}, -a_{10}^{p})$ and $(-a_{10}, -a_{11}, -a_{20})$. It is used in the Čerednik–Drinfeld part of the development, in the statement about elements of the $\eta$-piece with structure constants over the dual numbers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_not_exists_forall_period_variation_eq_mul_of_forall_ne_window.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.not_exists_forall_period_variation_eq_mul_of_forall_ne_window
    (p : ℕ) [Fact p.Prime] {κ : Type} [Field κ] [CharP κ p]
    {G : Type} [AddCommGroup G] (x₀ : G →+ κ)
    (a₁ a₁₀ a₁₁ a₂₀ s t r : κ) (ha₁ : a₁ ≠ 0)
    (hper : ∀ g : G, a₁ ^ p * x₀ g =
      (a₁ ^ p * a₁₀ + a₁ * a₁₁) * x₀ g ^ p + (a₁ ^ (p + 1) * a₂₀ - a₁ * a₁₀ ^ p * a₁₁) * x₀ g ^ (p ^ 2))
    (g₁ g₂ : G) (hind : ∀ c₁ c₂ : ℤ, c₁ • x₀ g₁ + c₂ • x₀ g₂ = 0 → (p : ℤ) ∣ c₁ ∧ (p : ℤ) ∣ c₂)
    (hwin : ∀ c₁ c₂ : κ,
      ¬ (s = c₁ * a₁ - c₂ * a₁₀ ∧ t = -(c₁ * a₁ ^ p) - c₂ * a₁₁ ∧ r = -(c₁ * a₁₀ ^ p) - c₂ * a₂₀)) :
    ¬ ∃ μ : κ, ∀ g : G,
      (a₁ ^ (p + 1) * r - a₁ * a₁₀ ^ p * t) * x₀ g ^ (p ^ 2) + (a₁ ^ p * s + a₁ * t) * x₀ g ^ p = μ * x₀ g := by sorry
