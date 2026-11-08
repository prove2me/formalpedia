-- Prove2me | Theorems.Thm_AddXnor_lemma_2
-- name    : AddXnor.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:57:39.724465+00:00
-- url     : https://prove2.me/theorems/75e31cf1-b930-4a4a-b42d-98892dc0f87d
-- title:
--   Lemma 2 (Normalization) — the update (3) of the normalized state
-- statement:
--   Let $E$ be the current value of a left-associative computation on $m$-bit words and $\varepsilon \in \{0,1\}$ the parity of the number of XNORs performed so far. Define $Y = E$ if $\varepsilon = 0$ and $Y = \overline{E}$ if $\varepsilon = 1$. On processing the next operand $a$:
--
--   1. the normalized pair evolves by
--   $$
--   (Y, \varepsilon) \longmapsto \begin{cases} (Y + (-1)^{\varepsilon} a \bmod 2^m,\ \varepsilon), & \text{for } +,\\ (Y \oplus a,\ \varepsilon \oplus 1), & \text{for } \odot;\end{cases} \qquad (3)
--   $$
--   2. consequently, if $2^p$ divides $a$, the lowest $p$ bits of $Y$ are unchanged;
--   3. a zero operand leaves $Y$ unchanged.
--
--   Normalization is what lets the soundness proof of Theorem 1 track a bit field through XNORs, which complement the actual value.
--
--   **Formalization Note** Clause 1 is stated as: for every operator bit $o$, the normalized form of the actual next state, with parity $\varepsilon \oplus o$, equals `normStep o (Y, ε) a`. Clauses 2 and 3 are stated for the actual next state, normalized with the new parity, for every $p \in \mathbb N$.
--
--   Differences from the source:
--   - encoding: $\varepsilon \in \{0,1\}$ and the operator in $\{+, \odot\}$ → Booleans, with the new parity $\varepsilon \oplus o$; reason: same cases
-- source:
--   Wang, Lv, Shen, Zhang, Add/XNOR Chains: An NP-Complete Boolean–Arithmetic Problem at the Meet-in-the-Middle Barrier, manuscript (sha256 405d6dda…), Lemma 2, equation (3), p.6 (PDF p.6)

import Mathlib
import Definitions.Def_AddXnor_chain
import Definitions.Def_AddXnor_normStep

namespace AddXnor

/-- **Lemma 2 (Normalization)** (Wang, Lv, Shen, Zhang, *Add/XNOR Chains*, manuscript, sha256 405d6dda…, Lemma 2, (3), p.6 (PDF p.6)). Let `E` be the current
value of a left-associative computation on `m`-bit words, `ε` the XNOR parity so far, and
`Y = normY ε E`. Processing the next operand `a` with operator `o` gives the new parity
`ε' = ε ⊕ o`, and:
1. the new normalized pair `(normY ε' (step o E a), ε')` is `normStep o (Y, ε) a`, i.e. (3);
2. if `2^p ∣ a`, the lowest `p` bits of `Y` are unchanged;
3. a zero operand leaves `Y` unchanged. -/
theorem lemma_2 {m : ℕ} (E a : BitVec m) (ε o : Bool) :
    (normY (ε ^^ o) (step o E a), ε ^^ o) = normStep o (normY ε E, ε) a ∧
    (∀ p : ℕ, 2 ^ p ∣ a.toNat →
      (normY (ε ^^ o) (step o E a)).toNat % 2 ^ p = (normY ε E).toNat % 2 ^ p) ∧
    (a = 0 → normY (ε ^^ o) (step o E a) = normY ε E) := by sorry

end AddXnor
