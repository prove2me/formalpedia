-- Prove2me | Theorems.Thm_CentralStrQ_lemma_9_13
-- name    : CentralStrQ.lemma_9_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:22:40.374251+00:00
-- url     : https://prove2.me/theorems/c2573f39-d139-45ef-a703-2f6d80993325
-- title:
--   Lemma 9.13 — unary profiles are reversed pieces of the PLCP bitvector
-- statement:
--   Let $T,\tau,S,k,(s_i),J_i,W$ be as in Definition 9.11, let $C\ge2\tau$, let $A$ be the $C$-capped LCE sequence of $S$ and $d=2\tau$. Write $q_i(p)=\mathrm{profile}_{A,W}(i)[p]$ and $U_i=\mathrm{unary\text{-}profile}_{A,W,d}(i)$. Then:
--
--   1. $\displaystyle\sum_{i=1}^k|U_i|\le 2N+2\tau\cdot\bigl|\{W[i]:i\in[1\,.\,.\,k]\}\bigr|$;
--   2. let $i\in[1\,.\,.\,k]$ and let $u\le v$ be integers in $[d\,.\,.\,|W[i]|]$ with $0<q_i(p)<C$ for every $p\in[u\,.\,.\,v]$, and put $j=s_i+d-v$, $j'=s_i+d-u$. Then $\mathrm{PLCP}_T[j]=v-d+q_i(v)$, and the reversal of the substring of $U_i$ from its $(u-d+1)$-th one to its $(v-d+1)$-th one equals the substring of $B^{\mathrm{PLCP}}_T$ from position $2j+\mathrm{PLCP}_T[j]$ to position $2j'+\mathrm{PLCP}_T[j']$.
--
--   The first claim bounds the total output length of the instance by $3N$; the second lets Proposition 9.14 copy pieces of the output into the bitvector.
--
--   Differences from the source:
--   - encoding: the (r)th one of U_i → select_{U_i}(r,1), asserted to exist; reason: Observation 8.7 gives the ones
--   - encoding: strings in Σⁿ with 1-based positions → lists over a linearly ordered type, 1-based access; reason: a Lean convention; same instances
-- source:
--   Kempa–Kociumaka, A Complete Characterization of Central String Queries in Compact Space, STOC 2027 submission (manuscript sha256 dea2f74f66f1bd686c8e3c6d4e11f36643253c3c86a04fc5faa1c3ac1c96f346), Lemma 9.13, pp.167–168 (PDF pp.168–169)

import Mathlib
import Definitions.Def_CentralStrQ_Strings
import Definitions.Def_CentralStrQ_PLCPBitvector
import Definitions.Def_CentralStrQ_LCPProfile
import Definitions.Def_CentralStrQ_SyncSet

set_option autoImplicit false

namespace CentralStrQ

/-- Kempa–Kociumaka, *A Complete Characterization of Central String Queries in Compact Space*, STOC 2027 submission (manuscript sha256 dea2f74f…c96f346), Lemma 9.13, pp.167–168 (PDF pp.168–169): "Let T, τ, S, k, (s_i)_{i∈[1..k]}, J_i, and W be
as in Definition 9.11. Let C ∈ ℤ≥2τ, let A be the C-capped LCE sequence of S, and denote d = 2τ. For
every i ∈ [1..k] and p ∈ [0..|W[i]|], denote q_i(p) = profile_{A,W}(i)[p] and
U_i = unary-profile_{A,W,d}(i) (Definitions 8.1 and 8.4). The following claims hold: 1. It holds
∑_{i=1}^k |U_i| ≤ 2N + 2τ · |{W[i] : i ∈ [1..k]}|. 2. Let i ∈ [1..k], and let u ≤ v be integers in
[d..|W[i]|] such that 0 < q_i(p) < C holds for every p ∈ [u..v]. Denote j = s_i + d − v and
j′ = s_i + d − u. Then PLCP_T[j] = v − d + q_i(v), and the reversal of the substring of U_i from its
(u − d + 1)th one to its (v − d + 1)th one is the substring of B^PLCP_T (Definition 9.1) from position
2j + PLCP_T[j] to position 2j′ + PLCP_T[j′]."

**Formalization Note.** `|{W[i]}|` is the number of distinct labels. The "(r)th one" of `U_i` is
`select_{U_i}(r, 1)`; the statement asserts that both ones exist, and the substring from position
`x` to position `y` (inclusive) is `factor U x (y + 1)`. -/
theorem lemma_9_13 {α : Type} [LinearOrder α] (T : List α) (τ : ℕ) (S : Finset ℕ) (C : ℕ)
    (hτ : 1 ≤ τ) (hτN : 3 * τ ≤ T.length) (hS : S.Nonempty) (hsync : IsSyncSet τ T S)
    (hC : 2 * τ ≤ C) :
    (∑ i ∈ Finset.Icc 1 S.card, (unaryProfile (cappedLCE T S C) (labels T τ S) (2 * τ) i).length ≤
      2 * T.length + 2 * τ * ((Finset.Icc 1 S.card).image (strAt (labels T τ S))).card) ∧
    ∀ i ∈ Finset.Icc 1 S.card, ∀ u v : ℕ, 2 * τ ≤ u → u ≤ v → v ≤ (strAt (labels T τ S) i).length →
      (∀ p ∈ Finset.Icc u v, 0 < profile (cappedLCE T S C) (labels T τ S) i p ∧
        profile (cappedLCE T S C) (labels T τ S) i p < C) →
      PLCP T (sAt T S i + 2 * τ - v) = v - 2 * τ + profile (cappedLCE T S C) (labels T τ S) i v ∧
      ∃ x y : ℕ,
        select (unaryProfile (cappedLCE T S C) (labels T τ S) (2 * τ) i) (u - 2 * τ + 1) true = x ∧
        select (unaryProfile (cappedLCE T S C) (labels T τ S) (2 * τ) i) (v - 2 * τ + 1) true = y ∧
        (factor (unaryProfile (cappedLCE T S C) (labels T τ S) (2 * τ) i) x (y + 1)).reverse =
          factor (plcpBits T) (2 * (sAt T S i + 2 * τ - v) + PLCP T (sAt T S i + 2 * τ - v))
            (2 * (sAt T S i + 2 * τ - u) + PLCP T (sAt T S i + 2 * τ - u) + 1) := by sorry

end CentralStrQ
