-- Prove2me | Theorems.Thm_DuanEP_Pure_log_count_concentration
-- name    : DuanEP.Pure.log_count_concentration
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:21:34.825821+00:00
-- url     : https://prove2.me/theorems/467b81f9-f2f5-424b-971c-adfe81dcca06
-- title:
--   Proof step: $\log f_J^{(m)}/m\to E$ in probability under $p_j=(1-\lambda^2)^m\lambda^{2j}f_j^{(m)}$
-- statement:
--   Let $r\in\mathbb R$, $\lambda=\tanh r$ and
--
--   $$
--   E_1=\cosh^2(r)\log\big(\cosh^2(r)\big)-\sinh^2(r)\log\big(\sinh^2(r)\big).
--   $$
--
--   For each $m$, let the outcome $J$ have the law $p^{(m)}_j=(1-\lambda^2)^m\lambda^{2j}f_j^{(m)}$, $j\in\mathbb N$. Then for every $\varepsilon>0$,
--
--   $$
--   \lim_{m\to\infty}\ \sum_{j\ge0}p^{(m)}_j\,\mathbf 1\Big[\big|\log f_j^{(m)}-mE_1\big|\le\varepsilon\,m\,E_1\Big]=1 ,
--   $$
--
--   that is, $\log f_J^{(m)}/m\to E_1$ in probability (with relative error $\varepsilon$).
--
--   This is the real-analytic content of the paper's claim "It can be easily proven that if $m$ goes to infinity, with unit probability we would get a maximally entangled state with entanglement $mE(|\Psi\rangle_{A_iB_i})$", once the outcome law, the outcome states and their entanglement $\log f_j^{(m)}$ have been identified.
--
--   **Formalization Note** The probability is a sum in $[0,\infty]$. Natural logarithms. At $r=0$, $E_1=0$ and the event is $f_J^{(m)}=1$.
--
--   Differences from the source:
--   - reading: "with unit probability" as m → ∞ → the probability of the event tends to 1 as m → ∞ (convergence in probability); reason: the outcome spaces change with m, so no almost-sure reading exists
--   - reading: "with entanglement mE" → |log f_J − mE₁| ≤ ε m E₁ for every ε > 0; reason: E grows linearly in m; only a relative statement is meaningful
--   - reading: a statement about states → its real-analytic core: the law p_j and E(|j⟩) = log f_j substituted; reason: this item is the proof step; the quantum translation is given by pair_entanglement, qnd_outcome_law and outcome_entanglement
--   - generalization: squeezing parameter r ≥ 0 (implicit) → every real r; reason: for r < 0, tanh r = −tanh|r| and the state is the |r| state up to the local phase (−1)^n on the B modes; the statement at r ≥ 0 is the paper's
--   - encoding: log of unstated base → natural logarithm Real.log (nats); reason: the paper does not fix a base; the claims hold in every base and the base-free goal is unaffected
-- source:
--   Duan, Giedke, Cirac, Zoller, Entanglement purification of Gaussian continuous variable quantum states, arXiv:quant-ph/9912017v2, p. 2, unnumbered (proof step of "It can be easily proven that if m goes to infinity, with unit probability ...")

import Mathlib
import Definitions.Def_DuanEP_Pure_fCount

open Filter Topology

namespace DuanEP.Pure

/-- Proof step of the asymptotic claim (Duan, Giedke, Cirac, Zoller, *Entanglement purification of Gaussian continuous variable quantum states*, arXiv:quant-ph/9912017v2, unnumbered, p. 2: "It can be easily proven that if
`m` goes to infinity, with unit probability we would get a maximally entangled state with
entanglement `mE(|Ψ⟩_{AᵢBᵢ})`"): under the outcome law `p_j = (1 − λ²)^m λ^{2j} f_j^{(m)}`,
`λ = tanh r`, the normalized entanglement `log f_J^{(m)} / m` of the outcome converges in probability
to `E₁ = cosh²(r) log(cosh²(r)) − sinh²(r) log(sinh²(r))`: for every `ε > 0`, the probability of
`|log f_J^{(m)} − m E₁| ≤ ε m E₁` tends to `1` as `m → ∞`.

**Formalization Note** Pure real analysis; no quantum object appears. The probability is a sum
in `ℝ≥0∞`. Every real `r` and every `ε > 0`; at `r = 0` (`E₁ = 0`) the event is `f_J^{(m)} = 1`.
Natural logarithms. -/
theorem log_count_concentration (r ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun m : ℕ => ∑' j : ℕ,
      ENNReal.ofReal ((1 - Real.tanh r ^ 2) ^ m * Real.tanh r ^ (2 * j) * fCount m j) *
        (if |Real.log (fCount m j) - m * (Real.cosh r ^ 2 * Real.log (Real.cosh r ^ 2) -
              Real.sinh r ^ 2 * Real.log (Real.sinh r ^ 2))|
            ≤ ε * m * (Real.cosh r ^ 2 * Real.log (Real.cosh r ^ 2) -
              Real.sinh r ^ 2 * Real.log (Real.sinh r ^ 2)) then 1 else 0))
      atTop (𝓝 1) := by sorry

end DuanEP.Pure
