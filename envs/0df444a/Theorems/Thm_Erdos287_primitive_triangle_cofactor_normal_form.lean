-- Prove2me | Theorems.Thm_Erdos287_primitive_triangle_cofactor_normal_form
-- name    : Erdos287.primitive_triangle_cofactor_normal_form
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T14:05:33.806397+00:00
-- url     : https://prove2.me/theorems/3b808d7a-9369-438a-bc7c-5a9f1a769452
-- title:
--   Normal form and lcm weights for a primitive adjacency triangle
-- statement:
--   Let the positive slopes $s_1,s_2,s_3$ have common gcd one, and put $g_{ij}=\gcd(s_i,s_j)$. Suppose $s_j r_i-s_i r_j=g_{ij}$ for all three pairs $i<j$. Then there are positive $u_i$ with $s_i=g_{ij}g_{ik}u_i$ for distinct $i,j,k$ and $u_2=u_1+u_3$. Moreover $\operatorname{lcm}(s_i,s_j)=g_{12}g_{13}g_{23}u_i u_j$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.primitive_triangle_cofactor_normal_form (s₁ s₂ s₃ : ℕ) (r₁ r₂ r₃ : ℤ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) (h₃ : 0 < s₃)
    (hprim : Nat.gcd (Nat.gcd s₁ s₂) s₃ = 1)
    (h₁₂ : (s₂ : ℤ) * r₁ - (s₁ : ℤ) * r₂ = ↑(Nat.gcd s₁ s₂))
    (h₂₃ : (s₃ : ℤ) * r₂ - (s₂ : ℤ) * r₃ = ↑(Nat.gcd s₂ s₃))
    (h₁₃ : (s₃ : ℤ) * r₁ - (s₁ : ℤ) * r₃ = ↑(Nat.gcd s₁ s₃)) :
    let g₁₂ := Nat.gcd s₁ s₂
    let g₁₃ := Nat.gcd s₁ s₃
    let g₂₃ := Nat.gcd s₂ s₃
    ∃ (u₁ u₂ u₃ : ℕ), 0 < u₁ ∧ 0 < u₂ ∧ 0 < u₃ ∧
      s₁ = g₁₂ * g₁₃ * u₁ ∧ s₂ = g₁₂ * g₂₃ * u₂ ∧ s₃ = g₁₃ * g₂₃ * u₃ ∧
      u₂ = u₁ + u₃ ∧
      Nat.lcm s₁ s₂ = g₁₂ * g₁₃ * g₂₃ * (u₁ * u₂) ∧
      Nat.lcm s₁ s₃ = g₁₂ * g₁₃ * g₂₃ * (u₁ * u₃) ∧
      Nat.lcm s₂ s₃ = g₁₂ * g₁₃ * g₂₃ * (u₂ * u₃) := by sorry
