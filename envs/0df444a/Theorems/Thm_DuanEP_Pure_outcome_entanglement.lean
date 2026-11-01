-- Prove2me | Theorems.Thm_DuanEP_Pure_outcome_entanglement
-- name    : DuanEP.Pure.outcome_entanglement
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:23:09.876283+00:00
-- url     : https://prove2.me/theorems/1cdf1f3c-1e1b-47e1-9df2-d7954bf279a9
-- title:
--   $|j\rangle$ is maximally entangled (dimension $f_j^{(m)}$) with $E(|j\rangle)=\log f_j^{(m)}$
-- statement:
--   Let $m\ge 1$ and $j\in\mathbb N$. The outcome state $|j\rangle_{(A_iB_i)}$ of Eq. (3) is a two-party maximally entangled state: its reduced density operator on side A is $1/f_j^{(m)}$ times the projection onto an $f_j^{(m)}$-dimensional subspace. Its entanglement is
--
--   $$
--   E\big(|j\rangle_{(A_iB_i)}\big)=\log\big(f_j^{(m)}\big).
--   $$
--
--   Together with the outcome law, this says that every outcome of the QND measurement yields a maximally entangled state of known entanglement.
--
--   **Formalization Note** Natural logarithm. The dimension $f_j^{(m)}$ is the number of terms in (3).
--
--   Differences from the source:
--   - encoding: m entangled pairs, i = 1, …, m → hypothesis 1 ≤ m; reason: the paper's setting has at least one pair; f_j^{(m)} = (j+m−1)!/(j!(m−1)!) is undefined at m = 0
--   - encoding: log of unstated base → natural logarithm Real.log (nats); reason: the paper does not fix a base; the claims hold in every base and the base-free goal is unaffected
--   - reading: "a two-party maximally entangled state" → IsMaximallyEntangled of dimension d = f_j^{(m)}: A-marginal = (1/d)·(projection onto a d-dimensional subspace), basis-free; reason: a pure state is maximally entangled iff its marginal is flat on its support; the dimension of (3) is its number of terms
-- source:
--   Duan, Giedke, Cirac, Zoller, Entanglement purification of Gaussian continuous variable quantum states, arXiv:quant-ph/9912017v2, p. 2, unnumbered ("two-party maximally entangled state |j⟩", "E(|j⟩) = log(f_j^(m))")

import Mathlib
import Definitions.Def_DuanEP_Pure_outcomeState
import Definitions.Def_DuanEP_Pure_entanglement
import Definitions.Def_DuanEP_Pure_IsMaximallyEntangled

namespace DuanEP.Pure

/-- The outcome state `|j⟩_{(AᵢBᵢ)}` is a two-party maximally entangled state (of dimension
`f_j^{(m)}`), and its entanglement is `E(|j⟩_{(AᵢBᵢ)}) = log(f_j^{(m)})`
(Duan, Giedke, Cirac, Zoller, *Entanglement purification of Gaussian continuous variable quantum states*, arXiv:quant-ph/9912017v2, unnumbered, p. 2).

**Formalization Note** Natural logarithm. The dimension `f_j^{(m)}` is the number of terms of
(3). The hypothesis `1 ≤ m` is the paper's setting; at `m = 0` and `j > 0` the state (3) is
empty. -/
theorem outcome_entanglement (m : ℕ) (hm : 1 ≤ m) (j : ℕ) :
    IsMaximallyEntangled (outcomeState m j) (fCount m j) ∧
      entanglement (outcomeState m j) = ENNReal.ofReal (Real.log (fCount m j)) := by sorry

end DuanEP.Pure
