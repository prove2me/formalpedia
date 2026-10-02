-- Prove2me | Theorems.Thm_ChebotarevDensity_classFunction_mem_span_fixCount
-- name    : ChebotarevDensity.classFunction_mem_span_fixCount
-- status  : Proved
-- author  : @vebis
-- created : 2026-10-01T14:26:30.665476+00:00
-- url     : https://prove2.me/theorems/92ba04ed-e0fa-42fd-9f5e-4d6fc0b58fd7
-- title:
--   Rational class functions are combinations of permutation characters
-- statement:
--   Let $G$ be a finite group and $\theta:G\to\mathbb R$ a function such that
--
--   1. $\theta$ is constant on conjugacy classes: $\theta(xgx^{-1})=\theta(g)$, and
--   2. $\theta(g^k)=\theta(g)$ whenever $k$ is coprime to the order of $g$.
--
--   For a subgroup $H\le G$ let $\pi_H(g)=\#\{xH\in G/H: gxH=xH\}$ be the permutation character of $G$ on $G/H$. Then there are finitely many subgroups $H\in S$ and real coefficients $c_H$ such that
--   $$\theta(g)=\sum_{H\in S}c_H\,\pi_H(g)\quad\text{for all }g\in G,\qquad \sum_{H\in S}c_H=\frac1{\#G}\sum_{g\in G}\theta(g).$$
--
--   This is a form of Artin's induction theorem: the real span of the permutation characters is the space of class functions that are constant on "rational classes" $\{g^k:\gcd(k,\operatorname{ord}g)=1\}$. The statement about the coefficients holds because every $\pi_H$ has average $1$ over $G$.
--
--   **Formalization Note** $\pi_H(g)$ is `fixCount H g`.
-- source:
--   Stevenhagen–Lenstra, Chebotarëv and his density theorem, Math. Intelligencer 18 (1996), no. 2, pp. 32–34 (Theorem of Frobenius, decomposition types, cycle patterns) and Appendix, pp. 35–36

import Definitions.Def_ChebotarevDensity_Aux

open Polynomial NumberField

namespace ChebotarevDensity

theorem classFunction_mem_span_fixCount {G : Type*} [Group G] [Fintype G] (θ : G → ℝ)
    (hconj : ∀ g x : G, θ (x * g * x⁻¹) = θ g)
    (hrat : ∀ (g : G) (k : ℕ), Nat.Coprime k (orderOf g) → θ (g ^ k) = θ g) :
    ∃ (S : Finset (Subgroup G)) (c : Subgroup G → ℝ),
      (∀ g : G, θ g = ∑ H ∈ S, c H * (fixCount H g : ℝ)) ∧
      ∑ H ∈ S, c H = (∑ g : G, θ g) / (Fintype.card G : ℝ) := by sorry

end ChebotarevDensity
