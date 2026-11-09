-- Prove2me | Theorems.Thm_CutRankSched_frontier_rule
-- name    : CutRankSched.frontier_rule
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:34:46.577189+00:00
-- url     : https://prove2.me/theorems/cbbdac70-e1aa-4dd3-8c52-9696e33f6436
-- title:
--   Section 5.1, rule (5) — frontier test and introduce/forget
-- statement:
--   Let $0 \le k < n$, let $i = k+1$, let $\lambda$ be a layer assignment and $t$ a trial layer. Then:
--
--   1. the frontier test (5), "$\lambda_j \ne t$ for all $j \in F^\circ_k$ with $\{j, i\} \in E(X^\circ)$", is equivalent to "$\lambda_j \ne t$ for all $j < i$ with $\{j, i\} \in E(X^\circ)$", so no earlier residual conflict is missed;
--   2. $F^\circ_{k+1} \subseteq F^\circ_k \cup \{i\}$, so keeping the old labels of events in $F^\circ_{k+1}$ and inserting $(i, t)$ when $i \in F^\circ_{k+1}$ yields labels on all of $F^\circ_{k+1}$.
--
--   Differences from the source:
--   - generalization: a positive integer budget L (Problem 3.2, p.5) → any L : ℕ, L = 0 included; reason: at L = 0 the statement still holds (no layer assignment of a nonempty trace exists, or the bound is trivial); for L ≥ 1 it is the source's claim
--   - generalization: stated for valid instances (Section 3.1's standing assumptions) → every instance, valid or not; reason: both facts are combinatorial properties of the frontier; valid instances are a special case
--   - reading: the procedural rule (5) with 'retain, insert, forget' and the claim that no conflict is missed → the equivalence of the test with all earlier residual constraints, and F°_{k+1} ⊆ F°_k ∪ {i}; reason: these are the two facts the rule asserts; the update itself is the definition next
--   - encoding: events 1..n and layers [L] = {1..L} → Fin n and Fin L (0-based; event i and layer t are the paper's i+1 and t+1); reason: index shift; same instances and assignments
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 5.1, Eq. (5), p.8

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_Residual
import Definitions.Def_CutRankSched_frontier

set_option autoImplicit false

namespace CutRankSched

/-- **Section 5.1, the frontier rule (5)** (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §5.1, Eq. (5), p.8). For event `i = k + 1` and a
trial layer `t`, the test (5) over the frontier `F°_k` is equivalent to `λ_j ≠ t` for **all**
earlier residual neighbours `j` of `i` (no earlier residual conflict is missed), and the new
frontier `F°_{k+1}` consists of old frontier events and possibly `i` (so retaining the old
labels in `F°_{k+1}` and inserting `(i, t)` gives the labels on `F°_{k+1}`).

**Formalization Note** 0-based: `i = ⟨k, hk⟩`, earlier events `j.val < k`. -/
theorem frontier_rule (I : Instance) (L k : ℕ) (hk : k < I.n) (lam : Fin I.n → Fin L) (t : Fin L) :
    ((∀ j ∈ frontier I k, Residual I j ⟨k, hk⟩ → lam j ≠ t) ↔
      (∀ j : Fin I.n, j.val < k → Residual I j ⟨k, hk⟩ → lam j ≠ t)) ∧
    frontier I (k + 1) ⊆ insert ⟨k, hk⟩ (frontier I k) := by sorry

end CutRankSched
