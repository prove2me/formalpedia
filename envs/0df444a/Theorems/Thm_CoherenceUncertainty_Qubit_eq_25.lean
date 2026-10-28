-- Prove2me | Theorems.Thm_CoherenceUncertainty_Qubit_eq_25
-- name    : CoherenceUncertainty.Qubit.eq_25
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:31.93726+00:00
-- url     : https://prove2.me/theorems/f43a2bf1-fda3-4a9c-a179-e27db55419e4
-- title:
--   Eq. (25), p. 11 — for c ∈ [1/2, 1]: |√(1 − c) − 1/2| ≤ |√c − 1/2| and f(√c) ≤ f(√(1 − c))
-- statement:
--   Let $p \in [0,1]$, $c \in [1/2, 1]$, and $f(x) = H(xp + (1-x)(1-p))$ with $H$ the binary entropy in bits. Then
--
--   $$\Big|\sqrt c - \tfrac12\Big| \ge \Big|\sqrt{1-c} - \tfrac12\Big| \qquad\text{and}\qquad f(\sqrt c) \le f(\sqrt{1-c}).$$
--
--   The second inequality compares the two candidate minima of $g = f(a) + f(b)$ in the proof of Theorem 2, the corners $A = B = 1 - \sqrt c$ and $A = B = \sqrt{1-c}$, and selects $f(0) + f(\sqrt c)$.
-- source:
--   Yuan, Bai, Peng & Ma, Quantum uncertainty relation using coherence, arXiv:1612.02573v2, p. 11, proof of Theorem 2, Eq. (25) and the sentence after it

import Mathlib
import Definitions.Def_ShadowTomography_QuantumLB_vnEntropy
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_CoherenceUncertainty_Qubit_Model

namespace CoherenceUncertainty.Qubit
theorem eq_25 (p c : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hc0 : 1 / 2 ≤ c) (hc1 : c ≤ 1) :
    |Real.sqrt (1 - c) - 1 / 2| ≤ |Real.sqrt c - 1 / 2| ∧
      fp p (Real.sqrt c) ≤ fp p (Real.sqrt (1 - c)) := by sorry
end CoherenceUncertainty.Qubit
