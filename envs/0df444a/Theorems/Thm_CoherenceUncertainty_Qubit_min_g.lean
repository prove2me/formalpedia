-- Prove2me | Theorems.Thm_CoherenceUncertainty_Qubit_min_g
-- name    : CoherenceUncertainty.Qubit.min_g
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:26.406701+00:00
-- url     : https://prove2.me/theorems/6eda96d1-aecf-4539-b2bc-07329485724e
-- title:
--   Proof of Theorem 2, pp. 11–12 — on Lemma 1's region, f(a) + f(b) ≥ f(0) + f(√c)
-- statement:
--   Let $p \in [0,1]$, $c \in [1/2, 1]$, and $f(x) = H(xp + (1-x)(1-p))$ with $H$ the binary entropy in bits. Let $a, b \in [0,1]$ satisfy the constraints of Lemma 1,
--
--   $$1 - \sqrt c \le a + b \le 1 + \sqrt c, \qquad |a - b| \le \sqrt{1 - c}.$$
--
--   Then
--
--   $$f(a) + f(b) \ge f(0) + f(\sqrt c).$$
--
--   This is the paper's statement that the minimal value of $g = f(a) + f(b)$ over the feasible region (Fig. 1) is $f(0) + f(\sqrt c)$. Since $f(0) = H(p) = H(\rho)$ and $f(\sqrt c) = H\big(p\sqrt c + (1-p)(1-\sqrt c)\big)$, it yields the bound of Theorem 2 through Eq. (26).
--
--   **Formalization Note.** The paper's displayed value $f(\sqrt c) = H(p\sqrt c + (1-p)\sqrt c)$ on p. 11 contains a misprint for $H(p\sqrt c + (1-p)(1-\sqrt c))$; only $f(0) + f(\sqrt c)$, as defined, is used here.
-- source:
--   Yuan, Bai, Peng & Ma, Quantum uncertainty relation using coherence, arXiv:1612.02573v2, pp. 11–12, proof of Theorem 2 ('the minimal value of g is given by f(0)+f(√c)'), Fig. 1

import Mathlib
import Definitions.Def_ShadowTomography_QuantumLB_vnEntropy
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_CoherenceUncertainty_Qubit_Model

namespace CoherenceUncertainty.Qubit
theorem min_g (p c a b : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hc0 : 1 / 2 ≤ c) (hc1 : c ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hlo : 1 - Real.sqrt c ≤ a + b) (hhi : a + b ≤ 1 + Real.sqrt c)
    (hdiff : |a - b| ≤ Real.sqrt (1 - c)) :
    fp p 0 + fp p (Real.sqrt c) ≤ fp p a + fp p b := by sorry
end CoherenceUncertainty.Qubit
