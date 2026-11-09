-- Prove2me | Theorems.Thm_CutRankSched_dp_invariant
-- name    : CutRankSched.dp_invariant
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:37:13.906754+00:00
-- url     : https://prove2.me/theorems/a9af513e-022a-4702-80c2-181c70061f79
-- title:
--   Proof of Theorem 5.2 — the DP invariant (soundness and completeness)
-- statement:
--   Let $L \ge 1$ and $0 \le k \le n$. The set of states held by Algorithm 1 after processing the first $k$ events equals
--   $$
--   \mathrm{DP}_k = \bigl\{ \bigl((U^k_s)_{s=1}^L, \lambda|_{F^\circ_k}\bigr) : \lambda \text{ satisfies (2) on the first } k \text{ events} \bigr\},
--   $$
--   the set of states (flag (9) and frontier labels) of the legal partial assignments. Every state the algorithm keeps comes from a legal partial assignment (soundness), and every legal partial assignment is represented (completeness).
--
--   Differences from the source:
--   - generalization: stated for valid instances (Section 3.1's standing assumptions) → every instance, valid or not; reason: the induction uses only the transition and the constraints (2); valid instances are a special case
--   - reading: the invariant (9) and the frontier invariant, then 'induction proves soundness and completeness' → equality of the algorithm's state set with the states of the legal partial assignments; reason: this is what soundness and completeness of the invariant state together
--   - encoding: partial assignments λ_1, …, λ_k → total maps Fin n → Fin L constrained only on the first k events; reason: the state reads only the first k values
--   - encoding: events 1..n and layers [L] = {1..L} → Fin n and Fin L (0-based; event i and layer t are the paper's i+1 and t+1); reason: index shift; same instances and assignments
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), proof of Theorem 5.2, p.10

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_State
import Definitions.Def_CutRankSched_stateOf
import Definitions.Def_CutRankSched_dpSet
import Definitions.Def_CutRankSched_LegalPrefix

set_option autoImplicit false

namespace CutRankSched

/-- **Proof of Theorem 5.2, the DP invariant** (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), proof of Theorem 5.2, p.10: "Initially, all
`U^0_s` are zero spaces and the frontier is empty. Assume the invariant (9) at cut `k`. … Induction
proves soundness and completeness."). For a positive budget `L` and every cut `0 ≤ k ≤ n`, the
states held by Algorithm 1 after `k` events are exactly the states `((U^k_s)_s, ℓ_k)` of the
partial assignments of the first `k` events that satisfy (2).

**Formalization Note** Partial assignments are total maps `Fin n → Fin L` constrained only on
`j.val < k` (`LegalPrefix`); `stateOf` reads only those values. `1 ≤ L` is the paper's
"positive integer `L`" (with `L = 0` and `n > 0` no map `Fin n → Fin 0` exists). -/
theorem dp_invariant (I : Instance) (L : ℕ) (hL : 1 ≤ L) (k : ℕ) (hk : k ≤ I.n) :
    dpSet I L k = {st | ∃ lam : Fin I.n → Fin L, LegalPrefix I L k lam ∧ st = stateOf I L k lam} := by sorry

end CutRankSched
