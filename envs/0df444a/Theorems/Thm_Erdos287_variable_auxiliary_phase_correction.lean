-- Prove2me | Theorems.Thm_Erdos287_variable_auxiliary_phase_correction
-- name    : Erdos287.variable_auxiliary_phase_correction
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T18:20:19.6367+00:00
-- url     : https://prove2.me/theorems/a684e958-77ec-5c08-8155-f5684bdc5dd3
-- title:
--   Independent auxiliary residues in the Type II phase
-- statement:
--   For a pair of progressions with shared main factor $B$ and independently chosen auxiliary residues $A_1,A_2$, compare their CRT representative $x$ with the reference representative $x_0$ using the main residue $a$ throughout. Under the displayed coprimality conditions the difference modulo $Bm_1m_2q_1q_2$ is the sum of the two explicit auxiliary corrections. The reference quotient satisfies the corresponding dispersion congruence.
-- source:
--   Erdős #287, mixed progression dispersion audit.

import Mathlib

theorem Erdos287.variable_auxiliary_phase_correction (B m₁ m₂ q₁ q₂ a A₁ A₂ x x₀ n₁ n₂ k : ℤ) (hB : B ≠ 0)
    (hdiff : n₁ - n₂ = B * k)
    (hm : IsCoprime m₁ m₂)
    (hc₁ : IsCoprime (B * m₁) n₁) (hc₂ : IsCoprime (B * m₂) n₂)
    (hn₁ : IsCoprime q₁ n₁) (hn₂ : IsCoprime q₂ n₂)
    (hqq : IsCoprime q₁ q₂)
    (hL₁ : IsCoprime (B * m₁ * m₂) q₁) (hL₂ : IsCoprime (B * m₁ * m₂) q₂)
    (h₁ : B * m₁ ∣ x * n₁ - a) (h₂ : B * m₂ ∣ x * n₂ - a)
    (ha₁ : q₁ ∣ x * n₁ - A₁) (ha₂ : q₂ ∣ x * n₂ - A₂)
    (hb₁ : B * (m₁ * q₁) ∣ x₀ * n₁ - a) (hb₂ : B * (m₂ * q₂) ∣ x₀ * n₂ - a) :
    let L := B * m₁ * m₂
    ∃ z₁ z₂ l : ℤ,
      (q₁ ∣ L * q₂ * n₁ * z₁ - 1) ∧
      (q₂ ∣ L * q₁ * n₂ * z₂ - 1) ∧
      (L * q₁ * q₂ ∣ x - x₀ - L * q₂ * (A₁ - a) * z₁ - L * q₁ * (A₂ - a) * z₂) ∧
      x₀ * n₁ = a + (m₁ * q₁) * B * l ∧
      (m₂ * q₂) * n₁ ∣ (m₁ * q₁) * n₂ * l - a * k := by sorry
