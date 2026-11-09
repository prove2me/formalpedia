-- Prove2me | Theorems.Thm_CutRankSched_legality_equivalence
-- name    : CutRankSched.legality_equivalence
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:35:32.559516+00:00
-- url     : https://prove2.me/theorems/a08ffda0-34ad-4f1d-ab29-3490b9a19f83
-- title:
--   Proof of Theorem 5.2 — the legality equivalence for (10)
-- statement:
--   Let $0 \le k < n$, $i = k+1$, $\lambda$ a layer assignment, $t$ a trial layer, and $U^k_t$ the flag (9) of $\lambda$ at cut $k$. Then
--   $$
--   U^k_t \subseteq \ker f_k \iff \forall j \le k\ (\lambda_j \ge t \Rightarrow A_{ji} = 0) \iff \forall j < i\ (A_{ji} = 1 \Rightarrow \lambda_j < t),
--   $$
--   where $f_k$ reads the coordinate of event $i$. So test (10) enforces exactly the new anticommutation precedences.
--
--   Differences from the source:
--   - generalization: a positive integer budget L (Problem 3.2, p.5) → any L : ℕ, L = 0 included; reason: at L = 0 the statement still holds (no layer assignment of a nonempty trace exists, or the bound is trivial); for L ≥ 1 it is the source's claim
--   - generalization: stated for valid instances (Section 3.1's standing assumptions) → every instance, valid or not; reason: the equivalence is linear algebra over F₂; valid instances are a special case
--   - encoding: signatures in F₂^{n−k}, f_k the first coordinate → zero-padded signatures in F₂^n, f_k the coordinate of event i; reason: linear injective embedding; same kernels
--   - encoding: events 1..n and layers [L] = {1..L} → Fin n and Fin L (0-based; event i and layer t are the paper's i+1 and t+1); reason: index shift; same instances and assignments
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), proof of Theorem 5.2, p.10

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_A
import Definitions.Def_CutRankSched_flagOf

set_option autoImplicit false

namespace CutRankSched

/-- **Proof of Theorem 5.2, legality equivalence** (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), proof of Theorem 5.2, p.10). For trial
layer `t` and `i = k + 1`,
`U^k_t ⊆ ker f_k ⟺ ∀ j ≤ k (λ_j ≥ t ⟹ A_ji = 0) ⟺ ∀ j < i (A_ji = 1 ⟹ λ_j < t)`.

**Formalization Note** 0-based events and layers; `U^k_t = flagOf I L k lam t` in the zero-padded
encoding, and `f_k` reads coordinate `i = ⟨k, hk⟩`. Both links of the chain are stated. -/
theorem legality_equivalence (I : Instance) (L k : ℕ) (hk : k < I.n) (lam : Fin I.n → Fin L)
    (t : Fin L) :
    ((∀ v ∈ flagOf I L k lam t, v ⟨k, hk⟩ = 0) ↔
      (∀ j : Fin I.n, j.val < k → t ≤ lam j → A I j ⟨k, hk⟩ = 0)) ∧
    ((∀ j : Fin I.n, j.val < k → t ≤ lam j → A I j ⟨k, hk⟩ = 0) ↔
      (∀ j : Fin I.n, j < ⟨k, hk⟩ → A I j ⟨k, hk⟩ = 1 → lam j < t)) := by sorry

end CutRankSched
