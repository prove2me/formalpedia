-- Prove2me | Theorems.Thm_AddXnor_gadgets_forced
-- name    : AddXnor.gadgets_forced
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:58:00.02321+00:00
-- url     : https://prove2.me/theorems/5cb2837f-df80-4630-baa8-7d15d5431abf
-- title:
--   Proof of Theorem 1, soundness — every gadget is $++++$ or $\mathrm{XXXX}$
-- statement:
--   Let $(s_1, \dots, s_r; T)$ be a Subset-Sum instance with $r \ge 1$, positive integers $s_i$, and $0 \le T \le S$, and consider an arbitrary operator sequence on which the instance (8) evaluates to zero. Then in every gadget $i$ the four operators applied to $U_i, V_i, U_i, V_i$ are equal: each gadget uses the pattern $++++$ or $\mathrm{XXXX}$.
--
--   In the paper this follows by induction on $i$ from Lemma 2 (later operands preserve the low $p_i + 4$ bits of $Y$), Lemma 5 (the guard field) and (10) (every normalized guard field must end at $1$).
--
--   **Formalization Note** Gadgets are 0-based: the operators of gadget $i < r$ are $x[4i], x[4i+1], x[4i+2], x[4i+3]$.
--
--   Differences from the source:
--   - encoding: gadgets $1, \dots, r$ → $0, \dots, r-1$, with operators $x[4i], \dots, x[4i+3]$; reason: 0-based lists, same positions
--   - encoding: $h = \lceil\log_2(S+1)\rceil$ → `Nat.size S`; reason: equal for every S ≥ 0
--   - encoding: the pattern $++++$ or $\mathrm{XXXX}$ → four equal list entries `x[4i]? = … = x[4i+3]?`; reason: the positions exist since x has length n − 1, so options are never none; same two patterns
-- source:
--   Wang, Lv, Shen, Zhang, Add/XNOR Chains: An NP-Complete Boolean–Arithmetic Problem at the Meet-in-the-Middle Barrier, manuscript (sha256 405d6dda…), proof of Theorem 1, "Soundness: gadgets are forced", p.11 (PDF p.11)

import Mathlib
import Definitions.Def_AddXnor_chain
import Definitions.Def_AddXnor_inst

namespace AddXnor

/-- **Gadgets are forced** (Wang, Lv, Shen, Zhang, *Add/XNOR Chains*, manuscript, sha256 405d6dda…, proof of Theorem 1, "Soundness: gadgets are forced", p.11
(PDF p.11)). For a Subset-Sum instance with `r ≥ 1`, positive `s_i`, `T ≤ S`, and any operator
string `x` of length `n − 1` on which the instance (8) evaluates to `0`: every gadget `i < r`
uses one operator four times, i.e. `x[4i] = x[4i+1] = x[4i+2] = x[4i+3]` (pattern `++++` or
`XXXX`).

**Formalization Note** 0-based gadgets: the operators of gadget `i` are `x[4i] … x[4i+3]`. -/
theorem gadgets_forced (s : List ℕ) (T : ℕ) (hs : s ≠ []) (hpos : ∀ a ∈ s, 0 < a)
    (hT : T ≤ S s) (x : List Bool) (hx : x.length = nOf s - 1)
    (h0 : chain (BitVec.ofNat (nOf s) (C s)) (x.zip (instRest s T)) = 0) :
    ∀ i < s.length, x[4 * i]? = x[4 * i + 1]? ∧ x[4 * i + 1]? = x[4 * i + 2]? ∧
      x[4 * i + 2]? = x[4 * i + 3]? := by sorry

end AddXnor
