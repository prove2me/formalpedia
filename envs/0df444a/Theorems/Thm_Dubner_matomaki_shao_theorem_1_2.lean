-- Prove2me | Theorems.Thm_Dubner_matomaki_shao_theorem_1_2
-- name    : Dubner.matomaki_shao_theorem_1_2
-- status  : Open
-- author  : @Idealson
-- created : 2026-11-24T12:11:42.3758+00:00
-- url     : https://prove2.me/theorems/87311967-ba3e-4960-a2df-e98c860fe1e5
-- title:
--   Matomäki–Shao: three primes with almost-twin partners
-- statement:
--   Every large enough integer $N\equiv3\pmod 6$ can be written $N=p_1+p_2+p_3$, where each $p_i$ is a prime such that $p_i+2$ is a product of at most two primes.
--
--   This is the ternary analogue of Dubner's conjecture with almost-twin primes.
-- source:
--   K. Matomäki, X. Shao, Vinogradov's three primes theorem with almost twin primes, Compositio Math. 153 (2017), arXiv:1512.03213, Theorem 1.2

import Mathlib
import Definitions.Def_Dubner_TwinPrimes

namespace Dubner
theorem matomaki_shao_theorem_1_2 :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → N % 6 = 3 →
      ∃ p₁ p₂ p₃ : ℕ, IsChenPrime p₁ ∧ IsChenPrime p₂ ∧ IsChenPrime p₃ ∧ N = p₁ + p₂ + p₃ := by
  sorry
end Dubner
