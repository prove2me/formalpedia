-- Prove2me | Theorems.Thm_CutRankSched_flag_update
-- name    : CutRankSched.flag_update
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:35:23.891928+00:00
-- url     : https://prove2.me/theorems/53f91e24-af92-45c2-b3d9-9a182ab4ea6c
-- title:
--   Proof of Theorem 5.2 — update (11) restores the invariant (9)
-- statement:
--   Let $0 \le k < n$, $i = k+1$, and extend a layer assignment $\lambda$ by $\lambda_i = t$. Then for every threshold $s$,
--   $$
--   U^{k+1}_s = \begin{cases} \rho_k(U^k_s) + \operatorname{span}\{b_i\}, & s \le t, \\ \rho_k(U^k_s), & s > t, \end{cases}
--   $$
--   where $U^k$ and $U^{k+1}$ are the flags (9) of the assignment before and after the extension, $\rho_k$ deletes the coordinate of $i$, and $b_i = (A_{i,i+1}, \dots, A_{i,n})$.
--
--   Differences from the source:
--   - generalization: a positive integer budget L (Problem 3.2, p.5) → any L : ℕ, L = 0 included; reason: at L = 0 the statement still holds (no layer assignment of a nonempty trace exists, or the bound is trivial); for L ≥ 1 it is the source's claim
--   - generalization: stated for valid instances (Section 3.1's standing assumptions) → every instance, valid or not; reason: the identity is linear algebra over F₂; valid instances are a special case
--   - encoding: ρ_k deletes a coordinate of F₂^{n−k} → ρ_k zeroes the coordinate of event i in zero-padded F₂^n; reason: linear injective embedding; same images and spans
--   - encoding: events 1..n and layers [L] = {1..L} → Fin n and Fin L (0-based; event i and layer t are the paper's i+1 and t+1); reason: index shift; same instances and assignments
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), proof of Theorem 5.2, p.10 (with (9) and (11), p.9)

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_signature
import Definitions.Def_CutRankSched_proj
import Definitions.Def_CutRankSched_flagOf

set_option autoImplicit false

namespace CutRankSched

/-- **Proof of Theorem 5.2, update (11) restores (9)** (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), proof of Theorem 5.2, p.10, with
(9) and (11), p.9). If the partial assignment `λ` is extended by `λ_i = t` for `i = k + 1`,
then the flag (9) at cut `k + 1` is obtained from the flag at cut `k` by the update (11):
`U^{k+1}_s = ρ_k(U^k_s) + span{b_i}` for `s ≤ t`, and `ρ_k(U^k_s)` for `s > t`.

**Formalization Note** 0-based: `i = ⟨k, hk⟩`; `ρ_k = proj n k`; `b_i = signature I (k+1) i`. -/
theorem flag_update (I : Instance) (L k : ℕ) (hk : k < I.n) (lam : Fin I.n → Fin L)
    (t s : Fin L) :
    flagOf I L (k + 1) (Function.update lam ⟨k, hk⟩ t) s =
      (flagOf I L k lam s).map (proj I.n k) ⊔
        (if s ≤ t then Submodule.span (ZMod 2) {signature I (k + 1) ⟨k, hk⟩} else ⊥) := by sorry

end CutRankSched
