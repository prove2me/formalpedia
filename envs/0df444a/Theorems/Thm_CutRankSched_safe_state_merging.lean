-- Prove2me | Theorems.Thm_CutRankSched_safe_state_merging
-- name    : CutRankSched.safe_state_merging
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:36:50.014701+00:00
-- url     : https://prove2.me/theorems/6b0d1a3e-974d-4c6e-ba44-df16a8f698c9
-- title:
--   Proof of Theorem 5.2 — safe state merging
-- statement:
--   Let $0 \le k \le n$, and let $\lambda, \lambda'$ be two assignments that satisfy (2) on the first $k$ events and have the same cut-$k$ state (flags (9) and frontier labels). Then for every suffix assignment $\mu$,
--   $$
--   \lambda \mid_k \mu \text{ satisfies (2)} \iff \lambda' \mid_k \mu \text{ satisfies (2)} .
--   $$
--   The two partial assignments have the same sets of allowable suffix assignments, which is what makes merging identical states safe.
--
--   Differences from the source:
--   - generalization: a positive integer budget L (Problem 3.2, p.5) → any L : ℕ, L = 0 included; reason: at L = 0 the statement still holds (no layer assignment of a nonempty trace exists, or the bound is trivial); for L ≥ 1 it is the source's claim
--   - generalization: stated for valid instances (Section 3.1's standing assumptions) → every instance, valid or not; reason: the argument uses only the constraints and the state; valid instances are a special case
--   - encoding: a partial assignment completed by a suffix assignment → the splice of two total maps at cut k; reason: same assignments
--   - encoding: events 1..n and layers [L] = {1..L} → Fin n and Fin L (0-based; event i and layer t are the paper's i+1 and t+1); reason: index shift; same instances and assignments
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), proof of Theorem 5.2, p.10

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_IsSchedule
import Definitions.Def_CutRankSched_stateOf
import Definitions.Def_CutRankSched_LegalPrefix
import Definitions.Def_CutRankSched_splice

set_option autoImplicit false

namespace CutRankSched

/-- **Proof of Theorem 5.2, safe state merging** (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), proof of Theorem 5.2, p.10). Take two
partial assignments of the first `k` events, both legal so far, whose cut-`k` flags and frontier
labels coincide. Then their sets of allowable suffix layer assignments coincide: a suffix `μ`
completes the first to a schedule iff it completes the second.

**Formalization Note** `splice k lam mu` follows `lam` on `j.val < k` and `mu` on the rest. -/
theorem safe_state_merging (I : Instance) (L k : ℕ) (hk : k ≤ I.n) (lam lam' : Fin I.n → Fin L)
    (h : LegalPrefix I L k lam) (h' : LegalPrefix I L k lam')
    (hs : stateOf I L k lam = stateOf I L k lam') :
    ∀ mu : Fin I.n → Fin L, IsSchedule I L (splice k lam mu) ↔ IsSchedule I L (splice k lam' mu) := by sorry

end CutRankSched
