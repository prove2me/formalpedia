-- Prove2me | Theorems.Thm_AddXnor_subset_recovery
-- name    : AddXnor.subset_recovery
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:58:11.567927+00:00
-- url     : https://prove2.me/theorems/6de0c55f-231e-47c0-bc9d-4aa265c88d2c
-- title:
--   Proof of Theorem 1, soundness — the gadgets using four additions form a subset summing to $T$
-- statement:
--   Let $(s_1, \dots, s_r; T)$ be a Subset-Sum instance with $r \ge 1$, positive integers $s_i$, and $0 \le T \le S$, and consider an arbitrary operator sequence on which the instance (8) evaluates to zero. Let $I$ consist of the gadgets using four additions. Then
--   $$
--   \sum_{i \in I} s_i = T,
--   $$
--   so $I$ solves the original Subset-Sum instance.
--
--   In the paper: zero operands preserve $Y$, the normalized value before $D$ is $C + 2^{K+1}\sum_{i\in I}s_i \pmod M$, and with (10) the difference $\sum_{i\in I}s_i - T$ is divisible by $2^h > S$, hence zero.
--
--   **Formalization Note** Gadgets are 0-based; $I = \{i < r : x[4i] = x[4i+1] = x[4i+2] = x[4i+3] = +\}$, and $s_i$ is `s.getD i 0`. The conclusion is the equality of natural numbers, so no subtraction occurs.
--
--   Differences from the source:
--   - encoding: gadgets $1, \dots, r$ → $0, \dots, r-1$, with operators $x[4i], \dots, x[4i+3]$; reason: 0-based lists, same positions
--   - encoding: $h = \lceil\log_2(S+1)\rceil$ → `Nat.size S`; reason: equal for every S ≥ 0
--   - encoding: the set $I$ of gadgets using four additions → a `Finset.range` filter over `x[4i]? = some false`, …, with $s_i$ as `s.getD i 0`; reason: same set, same sum
-- source:
--   Wang, Lv, Shen, Zhang, Add/XNOR Chains: An NP-Complete Boolean–Arithmetic Problem at the Meet-in-the-Middle Barrier, manuscript (sha256 405d6dda…), proof of Theorem 1, "Soundness: recovery of a subset", p.11 (PDF p.11)

import Mathlib
import Definitions.Def_AddXnor_chain
import Definitions.Def_AddXnor_inst

namespace AddXnor

/-- **Recovery of a subset** (Wang, Lv, Shen, Zhang, *Add/XNOR Chains*, manuscript, sha256 405d6dda…, proof of Theorem 1, "Soundness: recovery of a subset",
p.11 (PDF p.11)). For a Subset-Sum instance with `r ≥ 1`, positive `s_i`, `T ≤ S`, and any
operator string `x` of length `n − 1` on which the instance (8) evaluates to `0`: the set
`I = {i < r : x[4i] = x[4i+1] = x[4i+2] = x[4i+3] = +}` of gadgets using four additions
satisfies `∑_{i ∈ I} s_i = T`.

**Formalization Note** 0-based gadgets (operators `x[4i] … x[4i+3]`, `false` = `+`); `s_i` is
`s.getD i 0`. -/
theorem subset_recovery (s : List ℕ) (T : ℕ) (hs : s ≠ []) (hpos : ∀ a ∈ s, 0 < a)
    (hT : T ≤ S s) (x : List Bool) (hx : x.length = nOf s - 1)
    (h0 : chain (BitVec.ofNat (nOf s) (C s)) (x.zip (instRest s T)) = 0) :
    ∑ i ∈ (Finset.range s.length).filter (fun i => x[4 * i]? = some false ∧
        x[4 * i + 1]? = some false ∧ x[4 * i + 2]? = some false ∧ x[4 * i + 3]? = some false),
      s.getD i 0 = T := by sorry

end AddXnor
