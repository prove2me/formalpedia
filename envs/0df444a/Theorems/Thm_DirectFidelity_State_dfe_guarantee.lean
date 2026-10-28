-- Prove2me | Theorems.Thm_DirectFidelity_State_dfe_guarantee
-- name    : DirectFidelity.State.dfe_guarantee
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:47.683883+00:00
-- url     : https://prove2.me/theorems/33ad367b-110d-49a6-b440-75a256a4c95b
-- title:
--   p. 2 — with $\ell = \lceil 1/(\varepsilon^2\delta)\rceil$ and $m_i$ as in (6), $|\tilde Y - \mathrm{tr}(\rho\sigma)| \le 2\varepsilon$ with probability $\ge 1 - 2\delta$
-- statement:
--   **Direct fidelity estimation.** Let $\rho$ be a pure state and $\sigma$ an arbitrary state of $n$ qubits ($d = 2^n$), and let $\varepsilon,\delta>0$. Run the two-stage protocol:
--
--   1. draw $\ell = \lceil 1/(\varepsilon^2\delta)\rceil$ Pauli labels $k_1,\dots,k_\ell$ independently with probability $\Pr(k) = \chi_\rho(k)^2$, where $\chi_\rho(k) = \mathrm{tr}(\rho W_k/\sqrt d)$;
--   2. for each $i$, measure the Pauli observable $W_{k_i}$ on $m_i = \lceil \frac{2}{d\chi_\rho(k_i)^2\ell\varepsilon^2}\log(2/\delta)\rceil$ fresh copies of $\sigma$, obtaining independent outcomes $A_{ij}\in\{1,-1\}$ distributed by the Born rule, and output
--   $$\tilde Y = \frac1\ell\sum_{i=1}^\ell\frac{1}{m_i\sqrt d\,\chi_\rho(k_i)}\sum_{j=1}^{m_i}A_{ij}.$$
--
--   Then, with probability at least $1-2\delta$ over both stages,
--   $$\mathrm{tr}(\rho\sigma)\in\big[\tilde Y - 2\varepsilon,\ \tilde Y + 2\varepsilon\big].$$
--
--   Since $F(\rho,\sigma) = \mathrm{tr}(\rho\sigma)$ for pure $\rho$ (equation (1)), this certifies the fidelity of an experimentally prepared state $\sigma$ to a target pure state $\rho$ with a number of Pauli observables, $\ell$, independent of the number of qubits.
--
--   **Formalization Note.** The fidelity is written as $\mathrm{tr}(\rho\sigma)$ (the real part of the trace), which is (1) for pure $\rho$. The probability is the finite sum over label tuples $(k_1,\dots,k_\ell)$ of $\prod_i\Pr(k_i)$ times the probability, under the Born-rule product law of the outcomes, that $|\tilde Y - \mathrm{tr}(\rho\sigma)|\le2\varepsilon$. No hypothesis beyond the page's is added: for $\delta\ge1/2$ the claim is trivially true, and the tuples with some $\chi_\rho(k_i)=0$ have weight $0$.
-- source:
--   Flammia and Liu, Direct fidelity estimation from few Pauli measurements, arXiv:1104.4695v3, p. 2, §Fidelity Estimation, sentence after (8)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_DirectFidelity_State_Setting

namespace DirectFidelity.State

theorem dfe_guarantee (n : ℕ) (ρ σ : Matrix (Q n) (Q n) ℂ) (hρ : IsPure ρ)
    (hσ : WildeQIT.IsDensityOperator σ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    1 - 2 * δ ≤
      ∑ ks : Fin (ell ε δ) → P n, (∏ i, prob ρ (ks i)) *
        (outcomes σ ks (mVec ρ ε δ ks)).real
          {A | |Yt ρ ks (mVec ρ ε δ ks) A - ((ρ * σ).trace).re| ≤ 2 * ε} := by sorry

end DirectFidelity.State
