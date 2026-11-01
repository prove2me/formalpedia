-- Prove2me | Theorems.Thm_DuanEP_Pure_asymptotic_unit_efficiency
-- name    : DuanEP.Pure.asymptotic_unit_efficiency
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:24:19.813519+00:00
-- url     : https://prove2.me/theorems/540052ee-668c-4d03-9485-8530505f512f
-- title:
--   Asymptotic efficiency: with probability $\to1$ as $m\to\infty$ the QND outcome is maximally entangled with entanglement $\approx mE(|\Psi\rangle)$
-- statement:
--   Let $r\in\mathbb R$ and let $m$ pairs of modes $A_iB_i$ each be in the two-mode squeezed state $|\Psi\rangle_{A_iB_i}=\sqrt{1-\lambda^2}\sum_n\lambda^n|n\rangle_{A_i}|n\rangle_{B_i}$, $\lambda=\tanh r$, with entanglement $E=E(|\Psi\rangle_{A_iB_i})$. Side A measures the total excitation number $n_{A_1}+\dots+n_{A_m}$ (the projective measurement $\{P_j\otimes1_B\}$); outcome $j$ occurs with Born probability $p^{(m)}_j$ and leaves the post-measurement state $\psi^{(m)}_j$.
--
--   Then for every $\varepsilon>0$,
--
--   $$
--   \lim_{m\to\infty}\ \sum_{j\ge0}p^{(m)}_j\;\mathbf 1\Big[\psi^{(m)}_j\text{ is maximally entangled and }(1-\varepsilon)\,mE\le E\big(\psi^{(m)}_j\big)\le(1+\varepsilon)\,mE\Big]=1 .
--   $$
--
--   In words: as the number of pairs goes to infinity, with probability tending to one the protocol produces a maximally entangled state (in some finite dimension) whose entanglement is $mE(|\Psi\rangle_{A_iB_i})$ up to a relative error $\varepsilon$. This is property (i) of the paper: for pure states the protocol reaches the maximal allowed efficiency in the asymptotic limit.
--
--   **Formalization Note** Entanglement is the von Neumann entropy (natural logarithm) of the A-marginal, valued in $[0,\infty]$, and the probability is a sum in $[0,\infty]$; outcomes of probability $0$ contribute nothing. The maximally entangled dimension is existentially quantified.
--
--   Differences from the source:
--   - reading: "with unit probability" as m → ∞ → the Born probability of the good event tends to 1 as m → ∞ (convergence in probability); reason: the state spaces change with m, so no almost-sure reading exists
--   - reading: "with entanglement mE(|Ψ⟩)" → (1 − ε) m E ≤ E(post-measurement state) ≤ (1 + ε) m E for every ε > 0; reason: the entanglement increase ratio Γ_j/m → 1 in probability; an exact equality has probability → 0
--   - encoding: log of unstated base → natural logarithm Real.log (nats); reason: the paper does not fix a base; the claims hold in every base and the base-free goal is unaffected
--   - encoding: QND measurement of the total excitation number on side A → projective measurement {P_j ⊗ 1_B} with Born probabilities and normalized post-measurement states; reason: an ideal QND measurement of an observable with discrete spectrum is its projective measurement
--   - encoding: state vectors in Fock space → coefficient functions on Fock labels, normalization proved rather than typed; reason: avoids an ℓ²-membership proof inside the definitions; normalization is a conjunct of the milestones
--   - reading: "a maximally entangled state" → ∃ d, IsMaximallyEntangled ψ d: A-marginal = (1/d)·(projection onto a d-dimensional subspace), basis-free; reason: maximal entanglement of a pure state in a finite-dimensional space; d ≥ 1
--   - generalization: squeezing parameter r ≥ 0 (implicit) → every real r; reason: for r < 0, tanh r = −tanh|r| and the state is the |r| state up to the local phase (−1)^n on the B modes; the statement at r ≥ 0 is the paper's
--   - encoding: probability of an event → ∑_j p_j · 𝟙[event_j] in [0, ∞], with entanglements in [0, ∞] and bounds embedded by ENNReal.ofReal; reason: for ε ≥ 1 the lower bound is vacuous in both readings since entanglement is ≥ 0
-- source:
--   Duan, Giedke, Cirac, Zoller, Entanglement purification of Gaussian continuous variable quantum states, arXiv:quant-ph/9912017v2, p. 2, unnumbered ("It can be easily proven that if m goes to infinity, with unit probability we would get a maximally entangled state with entanglement mE(|Ψ⟩)"); property (i), p. 1

import Mathlib
import Definitions.Def_DuanEP_Pure_pairCoeff
import Definitions.Def_DuanEP_Pure_jointCoeff
import Definitions.Def_DuanEP_Pure_entanglement
import Definitions.Def_DuanEP_Pure_postState
import Definitions.Def_DuanEP_Pure_IsMaximallyEntangled

open Filter Topology

namespace DuanEP.Pure

open Classical in
/-- Asymptotic unit efficiency of the pure-state purification protocol
(Duan, Giedke, Cirac, Zoller, *Entanglement purification of Gaussian continuous variable quantum states*, arXiv:quant-ph/9912017v2, unnumbered, p. 2: "It can be easily proven that if `m` goes to infinity, with unit
probability we would get a maximally entangled state with entanglement `mE(|Ψ⟩_{AᵢBᵢ})`"; property
(i), p. 1). Let `m` pairs of modes each be in the two-mode squeezed state (1) with squeezing `r`, and
measure the total excitation number of the `A` side. For every `ε > 0`, the probability that the
post-measurement state is maximally entangled (in some finite dimension) and has entanglement between
`(1 − ε) m E(|Ψ⟩)` and `(1 + ε) m E(|Ψ⟩)` tends to `1` as `m → ∞`.

**Formalization Note** "With unit probability as `m → ∞`" is read as convergence of the probability
of the good event to `1` (the state spaces change with `m`); "with entanglement `mE`" is read with
relative error `ε`, for every `ε > 0`. The probability is `∑_j p_j 𝟙[event_j]` with the actual Born
probabilities `p_j` and the actual post-measurement states; outcomes of probability `0` contribute
`0`. Every real `r` (the paper has `r ≥ 0`). Natural logarithms. -/
theorem asymptotic_unit_efficiency (r ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun m : ℕ => ∑' j : ℕ, bornProb (jointCoeff m r) j *
      (if (∃ d : ℕ, IsMaximallyEntangled (postState (jointCoeff m r) j) d) ∧
          ENNReal.ofReal ((1 - ε) * m) * entanglement (pairCoeff r)
            ≤ entanglement (postState (jointCoeff m r) j) ∧
          entanglement (postState (jointCoeff m r) j)
            ≤ ENNReal.ofReal ((1 + ε) * m) * entanglement (pairCoeff r)
        then 1 else 0)) atTop (𝓝 1) := by sorry

end DuanEP.Pure
