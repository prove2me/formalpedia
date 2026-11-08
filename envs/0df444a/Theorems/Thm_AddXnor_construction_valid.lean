-- Prove2me | Theorems.Thm_AddXnor_construction_valid
-- name    : AddXnor.construction_valid
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:57:58.407142+00:00
-- url     : https://prove2.me/theorems/cb4948e7-f418-48d8-8f44-c13bf6e26f8f
-- title:
--   Proof of Theorem 1, Construction — (8) is a valid balanced instance
-- statement:
--   Let $(s_1, \dots, s_r; T)$ be a Subset-Sum instance with $r \ge 1$, positive integers $s_i$, and $0 \le T \le S = \sum_i s_i$, and let $h, p_i, K, n, C, P, U_i, V_i, M = 2^n, D$ be the constants (6)–(7). Then:
--
--   1. the sequence (8) has exactly $1 + 4r + (h+1) + 1 = n$ operands, each in $\{0, \dots, M-1\}$;
--   2. $C < 2^K$ and $S < 2^h$;
--   3. $0 < P \le C + 2^{K+1}S < 2^{K+h+1} = M$;
--   4. for every gadget $i$: $p_i \le K - 4$, $0 < U_i < 2^K$, and $0 < V_i < s_i 2^K < M$;
--   5. $0 < D < M$.
--
--   Hence (8) is a valid instance of the balanced problem: $n$ operands of $n$ bits each.
--
--   **Formalization Note** Gadgets are indexed from $0$ ($p_i = 2 + 4i$, $i < r$) and $s_i$ is `s.getD i 0`. $V_i = s_i 2^K - U_i$ and $D = 2^n - P$ are natural-number subtractions; the positivity clauses for $V_i$ and $D$ certify that they do not truncate.
--
--   Differences from the source:
--   - encoding: gadgets $1 \le i \le r$ with $p_i = 2 + 4(i-1)$ → gadgets $0 \le i < r$ with $p_i = 2 + 4i$; reason: 0-based lists, same constants
--   - encoding: $h = \lceil\log_2(S+1)\rceil$ → `Nat.size S`; reason: equal for every $S \ge 0$
-- source:
--   Wang, Lv, Shen, Zhang, Add/XNOR Chains: An NP-Complete Boolean–Arithmetic Problem at the Meet-in-the-Middle Barrier, manuscript (sha256 405d6dda…), proof of Theorem 1, "Construction", p.10 (PDF p.10)

import Mathlib
import Definitions.Def_AddXnor_inst

namespace AddXnor

/-- **(8) is a valid balanced instance** (Wang, Lv, Shen, Zhang, *Add/XNOR Chains*, manuscript, sha256 405d6dda…, proof of Theorem 1, "Construction", p.10
(PDF p.10)). For a Subset-Sum instance with `r ≥ 1`, positive `s_i` and `T ≤ S`: the list (8)
has exactly `n` operands, each `< 2^n = M`; `C < 2^K`, `S < 2^h`,
`0 < P ≤ C + 2^{K+1} S < 2^{K+h+1} = M`; for every gadget `i`, `p_i ≤ K − 4`,
`0 < U_i < 2^K` and `0 < V_i < s_i 2^K < M`; and `0 < D < M`.

**Formalization Note** 0-based gadget indices (`p_i = 2 + 4i`, `i < r`); `s_i` is
`s.getD i 0`. Positivity of `V_i` and `D` certifies that the natural-number subtractions in
(7) do not truncate. -/
theorem construction_valid (s : List ℕ) (T : ℕ) (hs : s ≠ []) (hpos : ∀ a ∈ s, 0 < a)
    (hT : T ≤ S s) :
    (instNat s T).length = nOf s ∧ (∀ w ∈ instNat s T, w < 2 ^ nOf s) ∧
    C s < 2 ^ KOf s ∧ S s < 2 ^ hOf s ∧
    0 < P s T ∧ P s T ≤ C s + 2 ^ (KOf s + 1) * S s ∧
    C s + 2 ^ (KOf s + 1) * S s < 2 ^ (KOf s + hOf s + 1) ∧
    (∀ i < s.length, pOf i ≤ KOf s - 4 ∧ 0 < U i ∧ U i < 2 ^ KOf s ∧
      0 < V s i ∧ V s i < s.getD i 0 * 2 ^ KOf s ∧ s.getD i 0 * 2 ^ KOf s < 2 ^ nOf s) ∧
    0 < D s T ∧ D s T < 2 ^ nOf s := by sorry

end AddXnor
