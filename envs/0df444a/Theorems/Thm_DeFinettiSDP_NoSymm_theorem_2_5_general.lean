-- Prove2me | Theorems.Thm_DeFinettiSDP_NoSymm_theorem_2_5_general
-- name    : DeFinettiSDP.NoSymm.theorem_2_5_general
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:46:43.00154+00:00
-- url     : https://prove2.me/theorems/2f2b1aef-2c38-493b-b567-9baad9b3a3e3
-- title:
--   Theorem 2.5, p. 9 — existence bound with a fixed measurement's distortion
-- statement:
--   Let $\rho$ be a state on $n=k+r$ copies of $B$, with $k\ge1$, and fix a finite-outcome POVM $M$ on $B$. Its side-information distortion is $D(M)$. For some number $m$ of measured systems with $0\le m\le r$, the random-subsystem product error satisfies
--
--   $$
--   E_m(\rho,M)\le kD(M)\sqrt{\frac{(2\ln2)(k-1)\log_2 d_B}{r+1}}.
--   $$
--
--   This is the first existence bound in Theorem 2.5 with the factor appropriate to a specified measurement. It is a bridge from the average estimate to the explicit two-design bound.
--
--   **Formalization Note** The printed theorem uses $f(B\mid\cdot)$ but does not specify $M$. Its proof chooses a measurement attaining that infimum, or the two-design measurement and its larger explicit factor. For an arbitrary $M$, the correct factor is $D(M)$. The inequality is in extended nonnegative reals, and $n-k+1=r+1$.
-- source:
--   Berta, Borderi, Fawzi & Scholz, arXiv:1810.12197v3, Theorem 2.5 p. 9 and proof p. 10

import Mathlib
import Definitions.Def_DeFinettiSDP_NoSymm_Random

namespace DeFinettiSDP.NoSymm

/-- First bound of Theorem 2.5, p. 9, for a fixed arbitrary POVM. The printed
statement leaves `M_B` unspecified while using the infimum `f(B|·)`; the proof
(p. 10) selects an optimal or a two-design measurement. For an arbitrary fixed
measurement, its own `distortion M` is the valid factor. The paper's `n` is
`k+r`, and its `n-k+1` is `r+1`. -/
theorem theorem_2_5_general {dB t : ℕ} (k r : ℕ) (hk : 1 ≤ k)
    (ρ : Matrix (Fin (k + r) → Fin dB) (Fin (k + r) → Fin dB) ℂ)
    (hρ : WildeQIT.IsDensityOperator ρ)
    (M : Fin t → Matrix (Fin dB) (Fin dB) ℂ)
    (hM : DeFinettiSDP.Hierarchy.IsPOVM M) :
    ∃ m : ℕ, m ≤ r ∧
      ENNReal.ofReal (rsError k r ρ M m) ≤
        (k : ENNReal) * DeFinettiSDP.Hierarchy.distortion M *
          ENNReal.ofReal
            (Real.sqrt (2 * Real.log 2 * ((k : ℝ) - 1) *
              Real.logb 2 (dB : ℝ) / ((r : ℝ) + 1))) := by sorry

end DeFinettiSDP.NoSymm
