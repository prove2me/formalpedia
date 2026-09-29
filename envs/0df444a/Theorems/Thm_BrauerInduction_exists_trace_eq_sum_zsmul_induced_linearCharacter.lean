-- Prove2me | Theorems.Thm_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter
-- name    : BrauerInduction.exists_trace_eq_sum_zsmul_induced_linearCharacter
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/05e51541-f585-5f16-a25e-19e53eb22b34
-- title:
--   Brauer's induction theorem in character form
-- statement:
--   Let $G$ be a finite group and let $\rho \colon G \to \mathrm{GL}_n(\mathbb{C})$ be a group homomorphism, for some natural number $n$ (so $n = 0$ is allowed, the indices being $\mathrm{Fin}\ n$). The assertion is that there exist a natural number $k$, a family of subgroups $H_i \le G$ indexed by $i \in \mathrm{Fin}\ k$, for each $i$ a group homomorphism $\psi_i \colon H_i \to \mathbb{C}^\times$, and integers $a_i$, such that for every $g \in G$ the trace of the matrix underlying $\rho(g)$ equals $$\sum_{i} a_i \cdot \frac{1}{\#H_i}\sum_{x \in G} \begin{cases} \psi_i(x^{-1}gx) & \text{if } x^{-1}gx \in H_i,\\ 0 & \text{otherwise,}\end{cases}$$ the integers $a_i$ and the cardinalities $\#H_i$ being taken in $\mathbb{C}$ and the values of $\psi_i$ regarded in $\mathbb{C}$ via $\mathbb{C}^\times \subseteq \mathbb{C}$. Thus the character of $\rho$ is an integral linear combination of the characters induced from one-dimensional characters of subgroups of $G$, with induction written out by Frobenius' explicit formula rather than through an induction operator. The subgroups $H_i$ and the characters $\psi_i$ are not required to be distinct, nor is any further property of them asserted.
--
--   This is Brauer's induction theorem, stated for characters of complex matrix representations of a finite group. The proof combines the decomposition of the constant class function $1$ as an integral combination of functions induced from hyperelementary subgroups with the description of characters of groups possessing a normal abelian subgroup with $p$-power-order quotient behaviour; the result feeds the construction of Artin $L$-functions, being used in [`ArtinL.exists_completedLSeries_functionalEquation_of_odd`](thm.html#ArtinL.exists_completedLSeries_functionalEquation_of_odd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

open scoped Classical in

theorem BrauerInduction.exists_trace_eq_sum_zsmul_induced_linearCharacter
    {G : Type} [Group G] [Fintype G] {n : ℕ} (ρ : G →* GL (Fin n) ℂ) :
    ∃ (k : ℕ) (H : Fin k → Subgroup G) (ψ : (i : Fin k) → (H i →* ℂˣ)) (a : Fin k → ℤ),
      ∀ g : G, ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace =
        ∑ i : Fin k, (a i : ℂ) * ((Nat.card (H i) : ℂ)⁻¹ *
          ∑ x : G, if hx : x⁻¹ * g * x ∈ H i then (((ψ i) ⟨x⁻¹ * g * x, hx⟩ : ℂˣ) : ℂ) else 0) := by sorry
