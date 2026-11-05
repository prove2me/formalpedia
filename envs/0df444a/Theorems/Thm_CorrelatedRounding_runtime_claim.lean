-- Prove2me | Theorems.Thm_CorrelatedRounding_runtime_claim
-- name    : CorrelatedRounding.runtime_claim
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:37:07.505415+00:00
-- url     : https://prove2.me/theorems/bb20268a-b3d0-46e4-ac3a-7e0fe7ce5ed7
-- title:
--   Proof of Theorem 1, p.11 — the runtime is $O(qK)$
-- statement:
--   There is a constant $C$ such that for all $q\ge1$, all $K$, every instance $u$ and every real vector $E$, the program of Algorithm 1 run on $(u,E)$ uses at most
--   $$C\,q\,K$$
--   ticks, assigns every item an FC, and its assignment is a valid output of Algorithm 1. The constant is chosen before the inputs.
--
--   This is the runtime clause of Theorem 1 as its own target.
--
--   Differences from the source:
--   - reading: "runtime O(qK)", with no machine model named → ∃ C : ℕ chosen before every input with ticks of the explicit program alg1Prog at most C·q·K; one tick per read of u, per read of a draw, per real operation and per loop iteration; reason: the inputs are real numbers, so the published real-RAM tick model is the natural reading; computing y from u is charged
--   - encoding: items i = 1,…,q, with q left implicit → the hypothesis 1 ≤ q; reason: the K draws cost K > 0 = C·0·K, so the bound needs q ≥ 1; K ≥ 1 then follows from the instance
--   - generalization: "Assume without loss that y_k > 0 for all k" (p.9) → an FC with y_k = 0 is allowed, and its entry of the draw is unconstrained; reason: such an FC has clock ∞ at every item; the page's instances, all y_k > 0, are a special case
--   - encoding: items i = 1,…,q and FCs k = 1,…,K → Fin q and Fin K, both 0-based; reason: Lean convention; same instances
-- source:
--   Ma, Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders, arXiv:2207.04774v4, proof of Theorem 1, p.11

import Mathlib
import Definitions.Def_CorrelatedRounding_IsInstance
import Definitions.Def_CorrelatedRounding_IsAlg1Output
import Definitions.Def_CorrelatedRounding_alg1Prog

namespace CorrelatedRounding

/-- **Runtime claim.** W. Ma, *Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders*, arXiv:2207.04774v4, proof of Theorem 1, p.11:
"The runtime is O(qK) because taking the arg min over k = 1,…,K for all i = 1,…,q is the bottleneck
operation in Algorithm 1."

There is a constant `C`, chosen before every input, such that for every `q ≥ 1`, `K`, instance `u` and real
vector `E`, the run of `alg1Prog u E` from counter `0` uses at most `C * q * K` ticks and returns `some` at
every item, the resulting assignment being a valid output of Algorithm 1.

**Formalization Note.** Real-RAM reading of "runtime"; see `alg1Prog`. `q = 0` is excluded because the `K`
draws cost `K > 0 = C * 0 * K`; the paper's items are `i = 1,…,q`. The bound covers computing `y` from `u`. -/
theorem runtime_claim :
    ∃ C : ℕ, ∀ (q K : ℕ), 1 ≤ q → ∀ (u : Fin K → Fin q → ℝ), IsInstance u → ∀ E : Fin K → ℝ,
      ((alg1Prog u E).run 0).2 ≤ C * q * K ∧
      ∃ z : Fin q → Fin K, (∀ i, ((alg1Prog u E).run 0).1 i = some (z i)) ∧ IsAlg1Output u E z := by sorry

end CorrelatedRounding
