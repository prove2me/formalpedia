-- Prove2me | Theorems.Thm_BlackwellDiscreteDP_Stationary_value_rational
-- name    : BlackwellDiscreteDP.Stationary.value_rational
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:02:02.955897+00:00
-- url     : https://prove2.me/theorems/1d52de44-e90c-4a0e-9630-a183424b337a
-- title:
--   Proof of Theorem 5 (p. 725) — each coordinate of V_β(f) is a rational function of β
-- statement:
--   For every decision rule $f$ and every state $s$, the $s$th coordinate of $V_\beta(f^{(\infty)})$ is a rational function of $\beta$ on $[0,1)$: there are real polynomials $p$ and $q$ such that $q(\beta)\ne0$ for all $\beta\in[0,1)$ and
--
--   $$V_{\beta,s}(f^{(\infty)})=\frac{p(\beta)}{q(\beta)}\qquad\text{for all }\beta\in[0,1).$$
--
--   In the proof of Theorem 5 this is what allows an inequality between returns that holds along a sequence of $\beta$'s tending to $1$ to be extended to all $\beta$ near $1$.
--
--   **Formalization Note.** The denominator is required to be nonzero on all of $[0,1)$; without this, $q=0$ would be a trivial witness because division by zero is $0$ in Lean.
-- source:
--   Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962), DOI 10.1214/aoms/1177704593, p. 725, §4, proof of Theorem 5

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_Stationary_Model

namespace BlackwellDiscreteDP.Stationary

/-- §4, proof of Theorem 5, p. 725 (unnumbered; Blackwell, *Discrete Dynamic Programming*, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593):
"For each s and f, the sth coordinate of V_β(f) is a rational function of β, as the
representation V = (I − βQ)⁻¹r shows."

For every decision rule `f` and state `s` there are real polynomials `p`, `q` such that `q`
does not vanish on `[0, 1)` and `V_β(f^(∞))_s = p(β)/q(β)` for every `β ∈ [0, 1)`.

**Formalization Note.** The nonvanishing of the denominator on all of `[0, 1)` is part of the
statement; without it `q = 0` would be a junk witness, since `x / 0 = 0` in Lean. -/
theorem value_rational {St Act : Type} [Fintype St] [DecidableEq St] [Nonempty St] [Fintype Act] [Nonempty Act]
    (M : Model St Act) :
    ∀ (f : St → Act) (s : St), ∃ p q : Polynomial ℝ,
      (∀ β : ℝ, 0 ≤ β → β < 1 → q.eval β ≠ 0) ∧
      ∀ β : ℝ, 0 ≤ β → β < 1 → M.V β (stationary f) s = p.eval β / q.eval β := by sorry

end BlackwellDiscreteDP.Stationary
