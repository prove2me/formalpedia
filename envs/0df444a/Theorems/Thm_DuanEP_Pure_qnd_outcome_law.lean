-- Prove2me | Theorems.Thm_DuanEP_Pure_qnd_outcome_law
-- name    : DuanEP.Pure.qnd_outcome_law
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:24:00.248608+00:00
-- url     : https://prove2.me/theorems/85688ac8-3bf8-48bd-a403-d35b88e576b4
-- title:
--   QND outcome law: probability $p_j=(1-\lambda^2)^m\lambda^{2j}f_j^{(m)}$ and post-measurement state $|j\rangle$
-- statement:
--   Let $m\ge 1$, $r\in\mathbb R$, $\lambda=\tanh r$, and let $|\Psi\rangle_{(A_iB_i)}$ be the joint state of $m$ two-mode squeezed pairs. Measure the total excitation number $n_{A_1}+\dots+n_{A_m}$ of side A (the projective measurement $\{P_j\otimes 1_B\}$). For every outcome $j\in\mathbb N$:
--
--   1. its Born probability is
--   $$
--   p_j=\big\|(P_j\otimes 1_B)|\Psi\rangle_{(A_iB_i)}\big\|^2=(1-\lambda^2)^m\lambda^{2j}f_j^{(m)};
--   $$
--   2. if $p_j>0$, the normalized post-measurement state is $|j\rangle_{(A_iB_i)}$ of Eq. (3) when $r\ge 0$, and $(-1)^j|j\rangle_{(A_iB_i)}$ when $r<0$.
--
--   So the measurement outcome $J$ has the negative binomial law $p_j$ and the measurement leaves the state $|j\rangle$.
--
--   **Formalization Note** The probability is the actual Born probability and the state the actual normalized projection, not their closed forms. For $r<0$, $\lambda<0$ and the global phase $(-1)^j$ appears; it does not affect entanglement.
--
--   Differences from the source:
--   - generalization: squeezing parameter r ≥ 0 (implicit) → every real r, with post-measurement state (−1)^j |j⟩ when r < 0; reason: for r ≥ 0 the statement is exactly the paper's (phase 1)
--   - encoding: m entangled pairs, i = 1, …, m → hypothesis 1 ≤ m; reason: the paper's setting has at least one pair; f_j^{(m)} = (j+m−1)!/(j!(m−1)!) is undefined at m = 0
--   - encoding: QND measurement of n_{A1} + ⋯ + n_{Am} → projective measurement {P_j ⊗ 1_B}: Born probability ‖(P_j ⊗ 1_B)Ψ‖², post-measurement state (P_j ⊗ 1_B)Ψ/‖·‖; reason: an ideal QND measurement of an observable with discrete spectrum is its projective measurement
--   - encoding: "projects onto |j⟩" for every j → post-measurement state identified only when p_j ≠ 0; reason: the normalized post-measurement state is undefined at probability 0
--   - encoding: probability p_j as a real number → Born probability in [0, ∞] equal to ENNReal.ofReal of the closed form; reason: the closed form is nonnegative; ℝ≥0∞ avoids a default value for non-summable families
-- source:
--   Duan, Giedke, Cirac, Zoller, Entanglement purification of Gaussian continuous variable quantum states, arXiv:quant-ph/9912017v2, p. 2, unnumbered ("The QND measurement projects the state ... with probability p_j")

import Mathlib
import Definitions.Def_DuanEP_Pure_jointCoeff
import Definitions.Def_DuanEP_Pure_postState
import Definitions.Def_DuanEP_Pure_outcomeState

namespace DuanEP.Pure

/-- The QND measurement of the total excitation number `n_{A₁} + ⋯ + n_{A_m}` on the `A` side
projects `|Ψ⟩_{(AᵢBᵢ)}` onto `|j⟩_{(AᵢBᵢ)}` with probability
`p_j = (1 − λ²)^m λ^{2j} f_j^{(m)}` (Duan, Giedke, Cirac, Zoller, *Entanglement purification of Gaussian continuous variable quantum states*, arXiv:quant-ph/9912017v2, unnumbered, p. 2).

**Formalization Note** The probability is the actual Born probability `‖(P_j ⊗ 1_B)Ψ‖²` and the state
is the actual normalized post-measurement state, for every outcome of positive probability. For
`r ≥ 0` (the paper's range) the post-measurement state is exactly `|j⟩`; for `r < 0`, where
`λ = tanh r < 0`, it is `(−1)^j |j⟩`. The hypothesis `1 ≤ m` is the paper's setting. -/
theorem qnd_outcome_law (m : ℕ) (hm : 1 ≤ m) (r : ℝ) (j : ℕ) :
    bornProb (jointCoeff m r) j =
        ENNReal.ofReal ((1 - Real.tanh r ^ 2) ^ m * Real.tanh r ^ (2 * j) * fCount m j) ∧
      (bornProb (jointCoeff m r) j ≠ 0 →
        postState (jointCoeff m r) j =
          fun p => (if r < 0 then (-1 : ℂ) ^ j else 1) * outcomeState m j p) := by sorry

end DuanEP.Pure
