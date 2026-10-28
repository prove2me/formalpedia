-- Prove2me | Theorems.Thm_DeFinettiSDP_NoSymm_eq_12
-- name    : DeFinettiSDP.NoSymm.eq_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:49:09.281605+00:00
-- url     : https://prove2.me/theorems/fc180dad-a287-4964-964c-1b84579df80a
-- title:
--   Equation (12), p. 10 — telescoping trace-norm bound for a product of marginals
-- statement:
--   Let $\tau$ be a state on $k$ ordered copies of a $d_B$-dimensional system. Let $\tau_{1:s}$ be its marginal on the first $s$ copies and $\tau_s$ its marginal on copy $s$. Then the distance from the product of all one-system marginals is bounded by the sum of successive correlation errors:
--
--   $$
--   \left\|\tau-\bigotimes_{s=1}^k\tau_s\right\|_1
--   \le\sum_{s=1}^k\left\|\tau_{1:s}-\tau_{1:s-1}\otimes\tau_s\right\|_1.
--   $$
--
--   This is the telescoping estimate used at the start of the proof of Theorem 2.5. It reduces the full product error to errors involving one new system at a time.
--
--   **Formalization Note** The paper applies (12) to conditional states. This item states the underlying inequality for every density operator. `Fin k` positions begin at zero, so its index `s` is the paper's $s+1$; the empty prefix is a one-dimensional trace-one state.
-- source:
--   Berta, Borderi, Fawzi & Scholz, arXiv:1810.12197v3, equation (12), p. 10

import Mathlib
import Definitions.Def_DeFinettiSDP_NoSymm_Random

namespace DeFinettiSDP.NoSymm

/-- Equation (12), p. 10, after removing the unchanged tensor factors using
`‖X ⊗ ω‖₁ = ‖X‖₁` for a state `ω`. Here the page's ordered `k` systems are the
coordinates of `Fin k → Fin dB`; `s : Fin k` corresponds to the page's `t = s+1`.
The page applies this to conditional states; the matrix inequality holds for every state. -/
theorem eq_12 {dB k : ℕ}
    (τ : Matrix (Fin k → Fin dB) (Fin k → Fin dB) ℂ)
    (hτ : WildeQIT.IsDensityOperator τ) :
    WildeQIT.traceNorm (τ - tensorFin (fun s => marg τ s)) ≤
      ∑ s : Fin k,
        WildeQIT.traceNorm
          (keepFirst τ (s.val + 1) (Nat.succ_le_of_lt s.isLt) - tensorStep τ s) := by sorry

end DeFinettiSDP.NoSymm
