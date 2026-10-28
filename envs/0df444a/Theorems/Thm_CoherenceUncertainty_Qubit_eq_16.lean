-- Prove2me | Theorems.Thm_CoherenceUncertainty_Qubit_eq_16
-- name    : CoherenceUncertainty.Qubit.eq_16
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:19.253515+00:00
-- url     : https://prove2.me/theorems/4e9e0935-e61a-422b-b19f-b7f9e30ae489
-- title:
--   Eq. (16), p. 8 — spectral form: H(X) = H(ap + (1 − a)(1 − p)), P = 2p² − 2p + 1, H(ρ) = H(p)
-- statement:
--   Let $\rho$ be a qubit state.
--
--   1. $\rho$ has a spectral decomposition $\rho = p\,|r\rangle\langle r| + (1-p)\,|r_\perp\rangle\langle r_\perp|$ with $p \in [0,1]$ and $\{|r\rangle, |r_\perp\rangle\}$ an orthonormal basis of $\mathbb C^2$.
--   2. For every such decomposition, every measurement basis $\mathbb X$ and every basis vector $|x\rangle \in \mathbb X$, with $a = |\langle r|x\rangle|^2$, the outcome entropy is
--   $$H(X) = H\big(ap + (1-a)(1-p)\big),$$
--   where on the right $H(t) = -t\log_2 t - (1-t)\log_2(1-t)$ is the binary entropy; the same holds for $\mathbb Z$ with $b = |\langle r|z\rangle|^2$.
--   3. The purity is $P = \operatorname{Tr}[\rho^2] = 2p^2 - 2p + 1$.
--   4. The von Neumann entropy is $H(\rho) = H(p)$.
--
--   These identities parametrize everything in Theorem 2 by the eigenvalue $p$ and the overlaps $a, b$; part 4 is the identity $H(p) = H(\rho)$ used in the last step of Eq. (26).
--
--   **Formalization Note.** The decomposition is written $\rho = W\,\operatorname{diag}(p, 1-p)\,W^\dagger$ with $W$ unitary, so $|r\rangle$ is the first column of $W$ and $\langle r|x_i\rangle = (W^\dagger U)_{0i}$. The paper's "$H(p) = H(\rho)$" appears in Eq. (26), p. 12, and is included here with the other spectral identities.
-- source:
--   Yuan, Bai, Peng & Ma, Quantum uncertainty relation using coherence, arXiv:1612.02573v2, p. 8, Eq. (16) and the purity P = 2p² − 2p + 1; H(p) = H(ρ) as used in Eq. (26), p. 12

import Mathlib
import Definitions.Def_ShadowTomography_QuantumLB_vnEntropy
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_CoherenceUncertainty_Qubit_Model

namespace CoherenceUncertainty.Qubit
theorem eq_16 (ρ : Mat2) (hρ : IsDensity ρ) :
    (∃ (p : ℝ) (W : MBasis), 0 ≤ p ∧ p ≤ 1 ∧
      ρ = (W : Mat2) * Matrix.diagonal ![(p : ℂ), 1 - (p : ℂ)] * star (W : Mat2)) ∧
    ∀ (p : ℝ) (W : MBasis), 0 ≤ p → p ≤ 1 →
      ρ = (W : Mat2) * Matrix.diagonal ![(p : ℂ), 1 - (p : ℂ)] * star (W : Mat2) →
      (∀ (U : MBasis) (i : Fin 2),
          shannon (prob U ρ) = fp p (‖(star (W : Mat2) * (U : Mat2)) 0 i‖ ^ 2)) ∧
        purity ρ = 2 * p ^ 2 - 2 * p + 1 ∧
        ShadowTomography.QuantumLB.vnEntropy ρ = WildeQIT.binaryEntropy p := by sorry
end CoherenceUncertainty.Qubit
