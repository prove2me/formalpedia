-- Prove2me | Theorems.Thm_ApproxDegComp_Supplement_theorem_33
-- name    : ApproxDegComp.Supplement.theorem_33
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:03:25.051208+00:00
-- url     : https://prove2.me/theorems/5fd2c77f-6883-4894-b01d-cfc1680e1f40
-- title:
--   Theorem 33 — no multiplicative composition for $Q_E$: $\frac{Q_E(f_k\circ\mathrm{OR}_{m_k})}{Q_E(f_k)\,Q_E(\mathrm{OR}_{m_k})}\to0$
-- statement:
--   **Exact quantum query complexity does not compose multiplicatively.** There exist total Boolean functions $f_k:\{0,1\}^{n_k}\to\{0,1\}$ and integers $m_k\ge0$ ($k\in\mathbb N$) such that $Q_E(f_k)>0$ and $Q_E(\mathrm{OR}_{m_k})>0$ for every $k$, and
--
--   $$\frac{Q_E(f_k\circ\mathrm{OR}_{m_k})}{Q_E(f_k)\,Q_E(\mathrm{OR}_{m_k})}\ \longrightarrow\ 0\qquad(k\to\infty).$$
--
--   Here $Q_E$ is the exact quantum query complexity and $f\circ\mathrm{OR}_m$ the block composition. Consequently no bound $Q_E(f\circ g)=\Omega(Q_E(f)\,Q_E(g))$ holds for all total $f,g$. The other measures behave differently: approximate degree composes multiplicatively (Theorem 23) and randomized query complexity does so up to a logarithm (Theorem 31 with Corollary 2).
--
--   **Formalization Note** The lengths $n_k$ are part of the existential. The convergence is that of the real sequence of ratios.
--
--   Differences from the source:
--
--   - reading: "Q_E(f_k ∘ OR_{m_k}) / (Q_E(f_k) Q_E(OR_{m_k})) → 0" → additionally Q_E(f_k) > 0 and Q_E(OR_{m_k}) > 0 for every k, with Filter.Tendsto of the real ratio to 0; reason: the ratio is a genuine quotient only for positive denominators, while Lean's 0/0 = 0 would let constant f_k witness the claim trivially; the paper's witnesses satisfy positivity (Q_E(f_k) = Ω((5/2)^k), Q_E(OR_{m_k}) = m_k ≥ 1), so this is the stronger reading
--   - encoding: total Boolean functions f_k and integers m_k → sequences n_k, m_k : ℕ → ℕ and f_k : (Fin n_k → Bool) → Bool; reason: OR_m is defined for m ≥ 0 and each f_k has its own input length
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), Theorem 33, p.37 (Definitions 12–14, p.13)

import Mathlib
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition
import Definitions.Def_ApproxDegComp_Supplement_orFn
import Definitions.Def_ApproxDegComp_Supplement_QE

namespace ApproxDegComp

namespace Supplement

/-- **Theorem 33**, p.37.
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Theorem 33, p.37: "There exist total Boolean functions f_k and
integers m_k such that Q_E(f_k ∘ OR_{m_k}) / (Q_E(f_k) Q_E(OR_{m_k})) → 0. Thus, no multiplicative
lower bound holds for the exact quantum query complexity."

**Formalization Note** `f_k` is a total function on `n_k` bits (`n_k` is part of the existential)
and `m_k ∈ ℕ`. The limit is `k → ∞` of the real ratio. Since Lean's `0 / 0 = 0` would make a
constant `f_k` a trivial witness, the statement also requires `Q_E(f_k) > 0` and
`Q_E(OR_{m_k}) > 0` for every `k`, i.e. that the ratio is a genuine quotient; the paper's
witnesses satisfy this (`Q_E(f_k) = Ω((5/2)^k)`, `Q_E(OR_{m_k}) = m_k ≥ 1`). `f ∘ OR_m` is the block
composition `OAI.Paper320.compose` and `Q_E` is Definitions 12–14. -/
theorem theorem_33 : ∃ (nk mk : ℕ → ℕ) (fk : (k : ℕ) → (Fin (nk k) → Bool) → Bool),
    (∀ k, 0 < QE (fk k)) ∧ (∀ k, 0 < QE (orFn (mk k))) ∧
    Filter.Tendsto
      (fun k => (QE (OAI.Paper320.compose (fk k) (orFn (mk k))) : ℝ) /
        ((QE (fk k) : ℝ) * (QE (orFn (mk k)) : ℝ)))
      Filter.atTop (nhds 0) := by sorry

end Supplement

end ApproxDegComp
