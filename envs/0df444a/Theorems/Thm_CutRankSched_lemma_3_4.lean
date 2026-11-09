-- Prove2me | Theorems.Thm_CutRankSched_lemma_3_4
-- name    : CutRankSched.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:34:37.22373+00:00
-- url     : https://prove2.me/theorems/8504d9d9-a0f3-4f87-8183-bc6dbaebf0cd
-- title:
--   Lemma 3.4 — every earlier residual neighbour remains visible
-- statement:
--   Let $0 \le k < n$ and let $i = k+1$ be the next event. If $j < i$ and $\{i, j\} \in E(X^\circ)$, then $j \in F^\circ_k$.
--
--   The event $i$ itself is the future neighbour that keeps $j$ on the frontier, so the frontier labels suffice to check every residual conflict of a newly placed event.
--
--   Differences from the source:
--   - generalization: stated for valid instances (Section 3.1's standing assumptions) → every instance, valid or not; reason: frontier membership is witnessed by i itself; valid instances are a special case
--   - encoding: events 1..n and layers [L] = {1..L} → Fin n and Fin L (0-based; event i and layer t are the paper's i+1 and t+1); reason: index shift; same instances and assignments
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Lemma 3.4, p.5

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_Residual
import Definitions.Def_CutRankSched_frontier

set_option autoImplicit false

namespace CutRankSched

/-- **Lemma 3.4 (Every earlier residual neighbor remains visible)** (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Lemma 3.4, p.5).
If `i = k + 1` and `j < i` with `{i, j} ∈ E(X°)`, then `j ∈ F°_k`.

**Formalization Note** 0-based: the paper's event `i = k + 1` is `⟨k, hk⟩ : Fin n`, and `j < i`
is `j.val < k`. -/
theorem lemma_3_4 (I : Instance) (k : ℕ) (hk : k < I.n) (j : Fin I.n) (hj : j.val < k)
    (hR : Residual I ⟨k, hk⟩ j) : j ∈ frontier I k := by sorry

end CutRankSched
