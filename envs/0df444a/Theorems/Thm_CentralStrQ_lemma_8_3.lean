-- Prove2me | Theorems.Thm_CentralStrQ_lemma_8_3
-- name    : CentralStrQ.lemma_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:21:24.17855+00:00
-- url     : https://prove2.me/theorems/4c134ce1-8ab2-43a5-ab86-2120414fd805
-- title:
--   Lemma 8.3 — LCP profiles are nonincreasing
-- statement:
--   Let $W[1\,.\,.\,m]$ be a sequence of strings and $A[1\,.\,.\,m)$ a sequence of nonnegative integers. For every $i\in[1\,.\,.\,m]$ and $p\in[0\,.\,.\,|W[i]|)$,
--   $$
--   \mathrm{profile}_{A,W}(i)[p+1]\ \le\ \mathrm{profile}_{A,W}(i)[p].
--   $$
--
--   Requiring a longer label prefix can only move the predecessor further back, so the minimum is over a longer range. It makes the unary encoding of Definition 8.4 well defined.
--
--   Differences from the source:
--   - encoding: sequences W[1..m], A[1..m) of nonnegative integers → lists with 1-based access, A of length m − 1 over ℕ, strings over any type with decidable equality; reason: a Lean convention; same instances
-- source:
--   Kempa–Kociumaka, A Complete Characterization of Central String Queries in Compact Space, STOC 2027 submission (manuscript sha256 dea2f74f66f1bd686c8e3c6d4e11f36643253c3c86a04fc5faa1c3ac1c96f346), Lemma 8.3, p.145 (PDF p.146)

import Mathlib
import Definitions.Def_CentralStrQ_LCPProfile

set_option autoImplicit false

namespace CentralStrQ

/-- Kempa–Kociumaka, *A Complete Characterization of Central String Queries in Compact Space*, STOC 2027 submission (manuscript sha256 dea2f74f…c96f346), Lemma 8.3, p.145 (PDF p.146): "Let W[1..m] be a sequence of strings, and let A[1..m) be a
sequence of nonnegative integers. For every i ∈ [1..m] and p ∈ [0..|W[i]|), it holds
profile_{A,W}(i)[p + 1] ≤ profile_{A,W}(i)[p]."

**Formalization Note.** `W` is a list of `m` strings over any alphabet with decidable equality,
`A` a list of `m − 1` natural numbers; indices are 1-based (`strAt`, `seqAt`). -/
theorem lemma_8_3 {α : Type} [DecidableEq α] (W : List (List α)) (A : List ℕ)
    (hA : A.length = W.length - 1) (i p : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ W.length)
    (hp : p < (strAt W i).length) : profile A W i (p + 1) ≤ profile A W i p := by sorry

end CentralStrQ
