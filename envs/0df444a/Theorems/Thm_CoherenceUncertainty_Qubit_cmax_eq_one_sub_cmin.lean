-- Prove2me | Theorems.Thm_CoherenceUncertainty_Qubit_cmax_eq_one_sub_cmin
-- name    : CoherenceUncertainty.Qubit.cmax_eq_one_sub_cmin
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:25.93543+00:00
-- url     : https://prove2.me/theorems/8eb64772-753c-4d51-80c4-7197321ef7bc
-- title:
--   pp. 8 and 11 — for two qubit measurement bases, c = 1 − c_min and c ≥ 1/2
-- statement:
--   Let $\mathbb X = \{|x_0\rangle, |x_1\rangle\}$ and $\mathbb Z = \{|z_0\rangle, |z_1\rangle\}$ be measurement bases of $\mathbb C^2$, and let $c = c_{\max} = \max_{i,j}|\langle x_i|z_j\rangle|^2$ and $c_{\min} = \min_{i,j}|\langle x_i|z_j\rangle|^2$. Then
--
--   $$c = 1 - c_{\min} \qquad\text{and}\qquad c \ge \tfrac12 .$$
--
--   The paper asserts the first identity on p. 8 when it introduces $c$ for Theorem 2, and uses $c \ge 1/2$ on p. 11 to derive Eq. (25). Both reflect that $|\langle x|z_0\rangle|^2 + |\langle x|z_1\rangle|^2 = 1$ in a two-dimensional space.
-- source:
--   Yuan, Bai, Peng & Ma, Quantum uncertainty relation using coherence, arXiv:1612.02573v2, p. 8 ('Note that we also have c = 1 − c_min') and p. 11 ('Because c ≥ 1/2')

import Mathlib
import Definitions.Def_ShadowTomography_QuantumLB_vnEntropy
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_CoherenceUncertainty_Qubit_Model

namespace CoherenceUncertainty.Qubit
theorem cmax_eq_one_sub_cmin (U V : MBasis) :
    cmax U V = 1 - cmin U V ∧ 1 / 2 ≤ cmax U V := by sorry
end CoherenceUncertainty.Qubit
