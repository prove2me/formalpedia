-- Prove2me | Theorems.Thm_CoherenceUncertainty_Qubit_eq_22
-- name    : CoherenceUncertainty.Qubit.eq_22
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:21.87806+00:00
-- url     : https://prove2.me/theorems/d462a98a-7132-4407-b412-cb1e8969514b
-- title:
--   Eq. (22), p. 10 — f(x) = H(xp + (1 − x)(1 − p)) is concave on [0, 1] and f(x) = f(1 − x)
-- statement:
--   Let $p \in [0,1]$ and let $H(t) = -t\log_2 t - (1-t)\log_2(1-t)$ be the binary entropy. Define $f(x) = H(xp + (1-x)(1-p))$. Then
--
--   1. $f$ is concave on $[0,1]$;
--   2. $f$ is symmetric about $x = 1/2$:
--   $$f(x) = f(1 - x) \quad \text{for every real } x.$$
--
--   The paper's proof of Theorem 2 reduces the bound to minimizing $g = f(a) + f(b)$, and these two properties of $f$ drive that minimization.
--
--   **Formalization Note.** Concavity is stated on $[0,1]$, where the argument $xp + (1-x)(1-p)$ stays in $[0,1]$; the symmetry holds for every real $x$ because the formula for $H$ is symmetric under $t \mapsto 1 - t$.
-- source:
--   Yuan, Bai, Peng & Ma, Quantum uncertainty relation using coherence, arXiv:1612.02573v2, p. 10, proof of Theorem 2, Eq. (22)

import Mathlib
import Definitions.Def_ShadowTomography_QuantumLB_vnEntropy
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_CoherenceUncertainty_Qubit_Model

namespace CoherenceUncertainty.Qubit
theorem eq_22 (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ConcaveOn ℝ (Set.Icc 0 1) (fp p) ∧ ∀ x : ℝ, fp p x = fp p (1 - x) := by sorry
end CoherenceUncertainty.Qubit
