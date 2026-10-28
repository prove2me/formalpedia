-- Prove2me | Theorems.Thm_CoherenceUncertainty_Qubit_lemma_1_eq_17
-- name    : CoherenceUncertainty.Qubit.lemma_1_eq_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:23.53498+00:00
-- url     : https://prove2.me/theorems/cc05ae86-1f7e-438b-821f-3d569f618bc5
-- title:
--   Lemma 1, Eq. (17), p. 8 — for unit |x⟩, |z⟩, |r⟩ ∈ ℂ^d: a + b ≤ 1 + √c and |a − b| ≤ √(1 − c)
-- statement:
--   Let $d$ be a natural number and let $|x\rangle, |z\rangle, |r\rangle \in \mathbb C^d$ be unit vectors. Define $a = |\langle r|x\rangle|^2$, $b = |\langle r|z\rangle|^2$ and $c = |\langle x|z\rangle|^2$. Then
--
--   $$a + b \le 1 + \sqrt c, \qquad |a - b| \le \sqrt{1 - c}.$$
--
--   The lemma bounds the squared overlaps of one vector $|r\rangle$ with two others by the overlap of those two. In the proof of Theorem 2 it confines $(a, b)$ to the region over which $f(a) + f(b)$ is minimized.
--
--   **Formalization Note.** $\mathbb C^d$ is `EuclideanSpace ℂ (Fin d)` with Mathlib's inner product `inner ℂ r x`, which is conjugate-linear in $r$, i.e. the bra-ket $\langle r|x\rangle$. By Cauchy–Schwarz $1 - c \ge 0$, so the square root is never evaluated at a negative number.
-- source:
--   Yuan, Bai, Peng & Ma, Quantum uncertainty relation using coherence, arXiv:1612.02573v2, p. 8, Lemma 1, Eq. (17)

import Mathlib
import Definitions.Def_ShadowTomography_QuantumLB_vnEntropy
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_CoherenceUncertainty_Qubit_Model

namespace CoherenceUncertainty.Qubit
theorem lemma_1_eq_17 (d : ℕ) (x z r : EuclideanSpace ℂ (Fin d))
    (hx : ‖x‖ = 1) (hz : ‖z‖ = 1) (hr : ‖r‖ = 1) :
    ‖inner ℂ r x‖ ^ 2 + ‖inner ℂ r z‖ ^ 2 ≤ 1 + Real.sqrt (‖inner ℂ x z‖ ^ 2) ∧
      |‖inner ℂ r x‖ ^ 2 - ‖inner ℂ r z‖ ^ 2| ≤ Real.sqrt (1 - ‖inner ℂ x z‖ ^ 2) := by sorry
end CoherenceUncertainty.Qubit
