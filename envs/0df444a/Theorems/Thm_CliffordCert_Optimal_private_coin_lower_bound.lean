-- Prove2me | Theorems.Thm_CliffordCert_Optimal_private_coin_lower_bound
-- name    : CliffordCert.Optimal.private_coin_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:48:56.077283+00:00
-- url     : https://prove2.me/theorems/6f01c73c-8d38-4757-86a9-e1bab5499a81
-- title:
--   Theorem 4 — arbitrary-channel private-coin lower bound
-- statement:
--   There are absolute real constants $c>0$ and $0<\varepsilon_0\le1$ such that for every $1\le q\le n$, $d=2^n$, $r=2^q$, and $0<\varepsilon\le\varepsilon_0$, any feasible uniform integer budget $m$ in the private-coin quantum-only model obeys
--   $$m\ge c\,d^3/(r^2\varepsilon^2).$$
--   Feasibility requires a valid protocol for every known reference and every promised alternative, while allowing the encoders and effect to depend on the reference. Arbitrary CPTP encoders and arbitrary independent private randomness are included. This is a worst-case obstruction over references, not a lower bound for every fixed reference.
--
--   This is the submission's Theorem 4, attributed there to [CDSW26], Theorem 5.8. Its original lower-bound proof is not reproduced in this submission.
--
--   Differences from the source:
--   - encoding: worst-case private-coin sample complexity Ω(d³/(r²ε²)) for sufficiently small absolute ε₀ → positive absolute constants quantified before n, q and ε and a lower bound for every uniform feasible integer budget; reason: this expands Ω without adding a numeric constant or incorrectly requiring every reference to be hard
-- source:
--   Hyunho Cha, Jungwoo Lee, STOC 2027 submission #226 (October 2026), p. 6, Theorem 4 ([CDSW26], Theorem 5.8); §A.2 p. 10 (PDF p. 11) (PDF p. 7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/226.pdf

import Definitions.Def_CliffordCert_Optimal_spectral_protocol
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace CliffordCert.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem private_coin_lower_bound :
    ∃ c ε₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧
      ∀ (n q : ℕ), 1 ≤ q → q ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ m : ℕ, FeasibleBudget (Bits n) (Bits q) ε m →
        c * (2 : ℝ)^(3*n) / ((2 : ℝ)^(2*q) * ε^2) ≤ (m : ℝ) := by sorry
end CliffordCert.Optimal
