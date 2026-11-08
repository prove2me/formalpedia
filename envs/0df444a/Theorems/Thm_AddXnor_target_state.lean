-- Prove2me | Theorems.Thm_AddXnor_target_state
-- name    : AddXnor.target_state
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:58:00.588527+00:00
-- url     : https://prove2.me/theorems/e1b531b0-849e-48bc-8e03-117d65940d7a
-- title:
--   Proof of Theorem 1, (10) — the last operator is $+$ and the state before $D$ is $P$ with $\varepsilon = 0$
-- statement:
--   Let $(s_1, \dots, s_r; T)$ be a Subset-Sum instance with $r \ge 1$, positive integers $s_i$, and $0 \le T \le S$, and consider an arbitrary operator sequence $x \in \{0,1\}^{n-1}$ on which the instance (8) evaluates to zero. Then:
--
--   1. the last operator, applied to $D$, is addition;
--   2. the number of XNORs among the first $n-2$ operators is even, i.e. $\varepsilon = 0$ immediately before $D$;
--   3. the state immediately before $D$ (after the first $n-1$ operands) is
--   $$
--   E = Y = P; \qquad (10)
--   $$
--   4. in particular, every normalized guard field (bits $p_i, \dots, p_i+3$ of that state) has final value $1$.
--
--   The proof in the paper uses the two control bits: every operand between $C$ and $D$ is divisible by $4$, $C \equiv 1$ and $D \equiv 3 \pmod 4$.
--
--   **Formalization Note** Operator positions are 0-based: $x[j]$ joins the state after $j+1$ operands to operand $w[j+1]$, so the last operator is $x[n-2]$; `false` is addition. The state before $D$ is the chain over the first $n-2$ operators; it is compared with $P$ as an $n$-bit word ($P < 2^n$ by the construction-bounds milestone).
--
--   Differences from the source:
--   - encoding: 1-based operators $O_1, \dots, O_{n-1}$ → 0-based $x[0], \dots, x[n-2]$; reason: same positions
--   - encoding: gadgets $1, \dots, r$ with $p_i = 2 + 4(i-1)$ → gadgets $0, \dots, r-1$ with $p_i = 2 + 4i$ and $s_i$ as `s.getD i 0`; reason: 0-based lists, same constants
--   - encoding: $h = \lceil\log_2(S+1)\rceil$ → `Nat.size S`; reason: equal for every S ≥ 0
--   - encoding: $\varepsilon = 0$, $E = Y = P$ → `Even` of the number of `true` among the first $n-2$ operators, and the chain value equal to `BitVec.ofNat n P`; reason: Y = E when the parity is even, and P < 2^n by the construction bounds; same claim
--   - encoding: the normalized guard field (bits $p_i, \dots, p_i+3$) → `(E.toNat / 2 ^ p_i) % 16`; reason: the field written as a number; Y = E since the parity is even
-- source:
--   Wang, Lv, Shen, Zhang, Add/XNOR Chains: An NP-Complete Boolean–Arithmetic Problem at the Meet-in-the-Middle Barrier, manuscript (sha256 405d6dda…), proof of Theorem 1, "Soundness: the last operation and the target state", (10), pp.10–11 (PDF pp.10–11)

import Mathlib
import Definitions.Def_AddXnor_chain
import Definitions.Def_AddXnor_inst

namespace AddXnor

/-- **The last operation and the target state** (Wang, Lv, Shen, Zhang, *Add/XNOR Chains*, manuscript, sha256 405d6dda…, proof of Theorem 1, "Soundness: the
last operation and the target state", (10), pp.10–11 (PDF pp.10–11)). For a Subset-Sum instance
with `r ≥ 1`, positive `s_i`, `T ≤ S`, let `x` be any operator string of length `n − 1` on
which the instance (8) evaluates to `0`. Then the last operator `x[n−2]` (the one applied to
`D`) is addition; the number of XNORs among the first `n − 2` operators is even (`ε = 0`); and
the state immediately before `D`, after the first `n − 1` operands, equals `P` (`E = Y = P`); and
in particular every guard field of that state (bits `p_i, …, p_i + 3`) has value `1`.

**Formalization Note** Operators are 0-based: `x[j]` joins the state after `j + 1` operands to
operand `w[j+1]`; `false` is addition. The guard field of gadget `i` is read off the word as
`(E.toNat / 2 ^ p_i) % 16`; since `ε = 0` here, the normalized field and the actual one coincide. -/
theorem target_state (s : List ℕ) (T : ℕ) (hs : s ≠ []) (hpos : ∀ a ∈ s, 0 < a)
    (hT : T ≤ S s) (x : List Bool) (hx : x.length = nOf s - 1)
    (h0 : chain (BitVec.ofNat (nOf s) (C s)) (x.zip (instRest s T)) = 0) :
    x[nOf s - 2]? = some false ∧ Even ((x.take (nOf s - 2)).count true) ∧
    chain (BitVec.ofNat (nOf s) (C s)) ((x.take (nOf s - 2)).zip (instRest s T)) =
      BitVec.ofNat (nOf s) (P s T) ∧
    ∀ i < s.length,
      ((chain (BitVec.ofNat (nOf s) (C s)) ((x.take (nOf s - 2)).zip (instRest s T))).toNat /
        2 ^ pOf i) % 16 = 1 := by sorry

end AddXnor
