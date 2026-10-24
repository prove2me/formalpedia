-- Prove2me | Theorems.Thm_DiazModulus_quadratic_complement_multiplication_matrix
-- name    : DiazModulus.quadratic_complement_multiplication_matrix
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-23T07:19:36.058657+00:00
-- url     : https://prove2.me/theorems/7ca6aac2-4dbc-4932-bbea-d64531ea4a5d
-- title:
--   Multiplication by k on span(1, u, u⁻¹, g₀, g₁) modulo span(1, u, u⁻¹): k·gⱼ = R(u)/u + Σ Tᵢⱼ gᵢ with deg R ≤ 2
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Let $k, g_0, g_1 \in \mathbb{C}$ with $kg_j \in \mathrm{span}(1, u, u^{-1}, g_0, g_1)$ for $j = 0, 1$. Then there are a $2 \times 2$ matrix $T$ over $\overline{\mathbb{Q}}$ and $R_0, R_1 \in \overline{\mathbb{Q}}[X]$ of degree at most $2$ with $kg_j = R_j(u)/u + T_{0j}g_0 + T_{1j}g_1$ for $j = 0, 1$.
--
--   As $\{R(u)/u : \deg R \leq 2\} = H_0 = \mathrm{span}(1, u, u^{-1})$, $T$ is a matrix of multiplication by $k$ modulo $H_0$. No dimension hypothesis is made, so $T$ need not be unique.
--
--   **Proof.** Peeling the five generators off the span one at a time writes $kg_j = a_j + b_ju + c_ju^{-1} + d_jg_0 + e_jg_1$ with coefficients in $\overline{\mathbb{Q}}$. Take $T_{0j} = d_j$, $T_{1j} = e_j$ and $R_j = b_jX^2 + a_jX + c_j$, of degree at most $2$; then $R_j(u)/u = a_j + b_ju + c_ju^{-1}$, since $u \neq 0$ ($0 \in \overline{\mathbb{Q}}$ and $u \notin \overline{\mathbb{Q}}$). Nothing else about $u$ is used, and no dimension hypothesis is needed for the existence of $T$ and $R$.
--
--   **Novelty.** Not found in the sources read; routine.
-- source:
--   Not found in the sources read. Part of Step 4 of the sheaf-free proof of Theorem NF. R20 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 23 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem quadratic_complement_multiplication_matrix (u k : ℂ) (hu : u ∉ Qbar) (g : Fin 2 → ℂ)
    (hk : ∀ j, k * g j ∈ Submodule.span Qbar ({1, u, u⁻¹, g 0, g 1} : Set ℂ)) :
    ∃ (T : Matrix (Fin 2) (Fin 2) ↥Qbar) (R : Fin 2 → (↥Qbar)[X]), ∀ j, (R j).natDegree ≤ 2 ∧
      k * g j = aeval u (R j) / u + (T 0 j : ℂ) * g 0 + (T 1 j : ℂ) * g 1 := by
  sorry

end DiazModulus
