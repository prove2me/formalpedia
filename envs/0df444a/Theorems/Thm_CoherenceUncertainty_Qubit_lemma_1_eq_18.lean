-- Prove2me | Theorems.Thm_CoherenceUncertainty_Qubit_lemma_1_eq_18
-- name    : CoherenceUncertainty.Qubit.lemma_1_eq_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:27.722177+00:00
-- url     : https://prove2.me/theorems/5521e794-1228-4370-b7e1-d2f7c65e238f
-- title:
--   Lemma 1, Eq. (18), p. 9 — for unit |x⟩, |z⟩, |r⟩ ∈ ℂ²: 1 − √c ≤ a + b
-- statement:
--   Let $|x\rangle, |z\rangle, |r\rangle \in \mathbb C^2$ be unit vectors and $a = |\langle r|x\rangle|^2$, $b = |\langle r|z\rangle|^2$, $c = |\langle x|z\rangle|^2$. Then
--
--   $$1 - \sqrt c \le a + b.$$
--
--   This is the second half of Lemma 1, valid only in dimension $d = 2$ (in $\mathbb C^3$, three orthonormal vectors give $a = b = c = 0$). Together with Eq. (17) it gives the lower edge $A = a + b \ge 1 - \sqrt c$ of the feasible region in the proof of Theorem 2.
-- source:
--   Yuan, Bai, Peng & Ma, Quantum uncertainty relation using coherence, arXiv:1612.02573v2, p. 9, Lemma 1, Eq. (18)

import Mathlib
import Definitions.Def_ShadowTomography_QuantumLB_vnEntropy
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_CoherenceUncertainty_Qubit_Model

namespace CoherenceUncertainty.Qubit
theorem lemma_1_eq_18 (x z r : EuclideanSpace ℂ (Fin 2))
    (hx : ‖x‖ = 1) (hz : ‖z‖ = 1) (hr : ‖r‖ = 1) :
    1 - Real.sqrt (‖inner ℂ x z‖ ^ 2) ≤ ‖inner ℂ r x‖ ^ 2 + ‖inner ℂ r z‖ ^ 2 := by sorry
end CoherenceUncertainty.Qubit
