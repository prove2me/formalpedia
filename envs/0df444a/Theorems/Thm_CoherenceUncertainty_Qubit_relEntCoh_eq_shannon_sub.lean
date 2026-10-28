-- Prove2me | Theorems.Thm_CoherenceUncertainty_Qubit_relEntCoh_eq_shannon_sub
-- name    : CoherenceUncertainty.Qubit.relEntCoh_eq_shannon_sub
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:21.111244+00:00
-- url     : https://prove2.me/theorems/4a15b953-574b-4297-99ea-c01ed7166383
-- title:
--   p. 8, after Theorem 2 — for a qubit state, C^X_RE(ρ) = H(X) − H(ρ)
-- statement:
--   Let $\rho$ be a qubit state and $\mathbb X = \{|x_0\rangle, |x_1\rangle\}$ a measurement basis of $\mathbb C^2$. Write $H(X) = -\sum_i p_i \log_2 p_i$ for the Shannon entropy of the outcome distribution $p_i = \langle x_i|\rho|x_i\rangle$, and $H(\rho)$ for the von Neumann entropy (in bits). Then the relative entropy of coherence of $\rho$ in the basis $\mathbb X$ equals
--
--   $$C^{\mathbb X}_{\mathrm{RE}}(\rho) = H(X) - H(\rho).$$
--
--   Since $C^{\mathbb X}_{\mathrm{RE}}(\rho) = H(\rho_{\mathrm{diag}}) - H(\rho)$ by definition, the content is that the dephased state $\rho_{\mathrm{diag}}$ has the outcome probabilities as its eigenvalues. This identity turns the quantum uncertainty relation (14) into the conventional entropic uncertainty relation (15).
-- source:
--   Yuan, Bai, Peng & Ma, Quantum uncertainty relation using coherence, arXiv:1612.02573v2, p. 8, sentence after Theorem 2 (before Eq. (15))

import Mathlib
import Definitions.Def_ShadowTomography_QuantumLB_vnEntropy
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_CoherenceUncertainty_Qubit_Model

namespace CoherenceUncertainty.Qubit
theorem relEntCoh_eq_shannon_sub (ρ : Mat2) (hρ : IsDensity ρ) (U : MBasis) :
    relEntCoh U ρ = shannon (prob U ρ) - ShadowTomography.QuantumLB.vnEntropy ρ := by sorry
end CoherenceUncertainty.Qubit
