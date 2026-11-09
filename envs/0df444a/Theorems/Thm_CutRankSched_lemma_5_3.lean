-- Prove2me | Theorems.Thm_CutRankSched_lemma_5_3
-- name    : CutRankSched.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:29:31.337984+00:00
-- url     : https://prove2.me/theorems/4d5ed826-adbe-4cc2-8780-c25cffb9967d
-- title:
--   Lemma 5.3, Eq. (12) — counting descending weak flags
-- statement:
--   Let $V$ be a vector space of dimension $q$ over $\mathbb F_2$ and $L \ge 0$. The number of weak flags $U_1 \supseteq \cdots \supseteq U_L$ of subspaces of $V$ satisfies
--   $$
--   \#\{\text{weak flags}\} \le \Bigl(\prod_{j=1}^q (2^j - 1)\Bigr) \binom{L+q}{q} \le 2^{q(q+1)/2} (L+1)^q . \tag{12}
--   $$
--   Both inequalities are asserted. The lemma bounds the number of flags a cut-rank state can hold.
--
--   **Formalization Note** A weak flag is an antitone map from $\{0, \dots, L-1\}$ to the subspaces of $V$.
--
--   Differences from the source:
--   - generalization: a positive integer budget L (Problem 3.2, p.5) → any L : ℕ, L = 0 included; reason: at L = 0 the statement still holds (no layer assignment of a nonempty trace exists, or the bound is trivial); for L ≥ 1 it is the source's claim
--   - encoding: weak flags U_1 ⊇ ⋯ ⊇ U_L indexed by [L] → antitone maps Fin L → Submodule (ZMod 2) V; reason: index shift; same flags
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Lemma 5.3, Eq. (12), p.11

import Mathlib

set_option autoImplicit false

namespace CutRankSched

/-- **Lemma 5.3, Eq. (12) (Counting descending weak flags)** (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Lemma 5.3, Eq. (12), p.11). In a
`q`-dimensional vector space over `𝔽₂`, the number of weak flags `U_1 ⊇ ⋯ ⊇ U_L` is at most
`(∏_{j=1}^q (2^j − 1)) · binom(L+q, q) ≤ 2^{q(q+1)/2} (L+1)^q`.

**Formalization Note** A weak flag is an antitone map `Fin L → Submodule (ZMod 2) V` (0-based
`s`). Both inequalities of (12) are stated. -/
theorem lemma_5_3 (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (q L : ℕ) (hq : Module.finrank (ZMod 2) V = q) :
    Nat.card {U : Fin L → Submodule (ZMod 2) V // Antitone U} ≤
        (∏ j ∈ Finset.Icc 1 q, (2 ^ j - 1)) * (L + q).choose q ∧
      (∏ j ∈ Finset.Icc 1 q, (2 ^ j - 1)) * (L + q).choose q ≤ 2 ^ (q * (q + 1) / 2) * (L + 1) ^ q := by sorry

end CutRankSched
