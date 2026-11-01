-- Prove2me | Theorems.Thm_DuanEP_Pure_pair_entanglement
-- name    : DuanEP.Pure.pair_entanglement
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:22:51.755322+00:00
-- url     : https://prove2.me/theorems/997a38cf-d3ff-4039-8aac-1bf4031dc3bc
-- title:
--   Normalization and entanglement $\cosh^2 r\log\cosh^2 r-\sinh^2 r\log\sinh^2 r$ of the two-mode squeezed state
-- statement:
--   Let $r\in\mathbb R$, $\lambda=\tanh r$, and let $|\Psi\rangle_{A_iB_i}=\sqrt{1-\lambda^2}\sum_{n\ge0}\lambda^n|n\rangle_{A_i}|n\rangle_{B_i}$ be the two-mode squeezed state of Eq. (1). Then:
--
--   1. the state is normalized: $\sum_{n,n'}|c_r(n,n')|^2=1$;
--   2. its entanglement, the von Neumann entropy of its reduced density operator on $A_i$, is
--
--   $$
--   E\big(|\Psi\rangle_{A_iB_i}\big)=\cosh^2(r)\log\big(\cosh^2(r)\big)-\sinh^2(r)\log\big(\sinh^2(r)\big).
--   $$
--
--   This is the per-pair entanglement $E$ against which the asymptotic yield $mE$ of the purification protocol is measured.
--
--   **Formalization Note** Natural logarithms; at $r=0$ the term $\sinh^2(0)\log\sinh^2(0)$ is $0$. The entanglement is valued in $[0,\infty]$ and the closed form, which is nonnegative, is embedded by `ENNReal.ofReal`.
--
--   Differences from the source:
--   - generalization: squeezing parameter r ≥ 0 (implicit) → every real r; reason: for r < 0, tanh r = −tanh|r| and the state is the |r| state up to the local phase (−1)^n on the B modes; the statement at r ≥ 0 is the paper's
--   - encoding: log of unstated base → natural logarithm Real.log (nats); reason: the paper does not fix a base; the claims hold in every base and the base-free goal is unaffected
--   - encoding: state vectors in Fock space → coefficient functions on Fock labels, normalization proved rather than typed; reason: avoids an ℓ²-membership proof inside the definitions; normalization is a conjunct of the milestones
-- source:
--   Duan, Giedke, Cirac, Zoller, Entanglement purification of Gaussian continuous variable quantum states, arXiv:quant-ph/9912017v2, p. 1, unnumbered, after Eq. (1)

import Mathlib
import Definitions.Def_DuanEP_Pure_pairCoeff
import Definitions.Def_DuanEP_Pure_entanglement

open scoped ENNReal

namespace DuanEP.Pure

/-- The two-mode squeezed state (1) is normalized and its entanglement is
`E(|Ψ⟩_{AᵢBᵢ}) = cosh²(r) log(cosh²(r)) − sinh²(r) log(sinh²(r))`
(Duan, Giedke, Cirac, Zoller, *Entanglement purification of Gaussian continuous variable quantum states*, arXiv:quant-ph/9912017v2, unnumbered, p. 1, after Eq. (1)).

**Formalization Note** Every real `r` (the paper has `r ≥ 0`; the formula is even in `r`).
Logarithms are natural. At `r = 0` the term `sinh²(0) log(sinh²(0))` is `0 · log 0 = 0`, as in the
convention `0 log 0 = 0`, and Lean's `Real.log 0 = 0` agrees. The right side is nonnegative, so
`ENNReal.ofReal` loses nothing. -/
theorem pair_entanglement (r : ℝ) :
    HasSum (fun p : ℕ × ℕ => ‖pairCoeff r p‖ ^ 2) 1 ∧
      entanglement (pairCoeff r) = ENNReal.ofReal
        (Real.cosh r ^ 2 * Real.log (Real.cosh r ^ 2) - Real.sinh r ^ 2 * Real.log (Real.sinh r ^ 2)) := by sorry

end DuanEP.Pure
