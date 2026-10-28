-- Prove2me | Theorems.Thm_CoherenceUncertainty_Qubit_theorem_2
-- name    : CoherenceUncertainty.Qubit.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:20.592564+00:00
-- url     : https://prove2.me/theorems/32b89111-2a17-4962-84b7-ef2df2ed2fda
-- title:
--   Theorem 2, p. 8 — for a qubit state, C^X_RE(ρ) + C^Z_RE(ρ) ≥ H((√(2P−1)(2√c−1)+1)/2) − H(ρ)
-- statement:
--   Let $\rho$ be a qubit state and let $\mathbb X = \{|x\rangle\}$ and $\mathbb Z = \{|z\rangle\}$ be two measurement bases of $\mathbb C^2$. Write $P = \operatorname{Tr}[\rho^2]$ for the purity of $\rho$, $c = \max_{|x\rangle\in\mathbb X, |z\rangle\in\mathbb Z} |\langle x|z\rangle|^2$ for the maximal overlap of the bases, $C^{\mathbb X}_{\mathrm{RE}}(\rho) = H(\rho_{\mathrm{diag}}) - H(\rho)$ for the relative entropy of coherence in the basis $\mathbb X$ (with $\rho_{\mathrm{diag}}$ the state dephased in that basis), $H(\rho)$ for the von Neumann entropy and $H(t) = -t\log_2 t - (1-t)\log_2(1-t)$ for the binary entropy, all in bits. Then
--
--   $$C^{\mathbb X}_{\mathrm{RE}}(\rho) + C^{\mathbb Z}_{\mathrm{RE}}(\rho) \ \ge\ H\!\left(\frac{\sqrt{2P-1}\,(2\sqrt c - 1) + 1}{2}\right) - H(\rho).$$
--
--   This is the quantum uncertainty relation for the relative entropy of coherence: the coherence of a qubit state in two bases cannot both be small unless the bases nearly coincide ($c$ close to $1$) or the state is nearly maximally mixed ($P$ close to $1/2$). The bound depends on the state only through its purity and its von Neumann entropy, and it is attained by the maximally mixed state.
--
--   **Formalization Note.** States are $2\times 2$ density matrices and bases are $2\times2$ unitaries (columns = basis vectors). On these objects $2P - 1 \in [0,1]$ and $c \in [1/2, 1]$, so neither square root is evaluated at a negative number and the argument of $H$ lies in $[1/2, 1]$. No hypothesis is added beyond "qubit state" and "two measurement bases".
-- source:
--   Yuan, Bai, Peng & Ma, Quantum uncertainty relation using coherence, arXiv:1612.02573v2, p. 8, Theorem 2, Eq. (14)

import Mathlib
import Definitions.Def_ShadowTomography_QuantumLB_vnEntropy
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_CoherenceUncertainty_Qubit_Model

namespace CoherenceUncertainty.Qubit
theorem theorem_2 (ρ : Mat2) (hρ : IsDensity ρ) (U V : MBasis) :
    WildeQIT.binaryEntropy
          ((Real.sqrt (2 * purity ρ - 1) * (2 * Real.sqrt (cmax U V) - 1) + 1) / 2)
        - ShadowTomography.QuantumLB.vnEntropy ρ
      ≤ relEntCoh U ρ + relEntCoh V ρ := by sorry
end CoherenceUncertainty.Qubit
