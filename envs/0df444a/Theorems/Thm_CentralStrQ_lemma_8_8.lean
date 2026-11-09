-- Prove2me | Theorems.Thm_CentralStrQ_lemma_8_8
-- name    : CentralStrQ.lemma_8_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:21:27.296322+00:00
-- url     : https://prove2.me/theorems/f1e303dc-a3c6-4ed3-b491-9d2eb29d140a
-- title:
--   Lemma 8.8 — refinement of LCP profiles
-- statement:
--   Let $W[1\,.\,.\,m]$ be a sequence of strings and $A[1\,.\,.\,m)$ a sequence of nonnegative integers. Let $i\in[1\,.\,.\,m]$ and $p\in[0\,.\,.\,|W[i]|)$ be such that $h=\mathrm{prefix\text{-}special\text{-}pred}_W(i,p+1)\ne-\infty$. Then
--   $$
--   \mathrm{profile}_{A,W}(i)[p+1]=\min\{\mathrm{profile}_{A,W}(y)[p] : y\in(h\,.\,.\,i] \text{ and } W[y] \text{ has prefix } W[i][1\,.\,.\,p]\}.
--   $$
--
--   The profile values for prefix length $p+1$ are thus minima of values for prefix length $p$; the construction of Section 8 computes the profiles one prefix length at a time on this basis.
--
--   Differences from the source:
--   - encoding: the minimum of a finite nonempty set → IsLeast: the value belongs to the set and is at most each member; reason: the set contains y = i
--   - encoding: sequences W[1..m], A[1..m) of nonnegative integers → lists with 1-based access, A of length m − 1 over ℕ, strings over any type with decidable equality; reason: a Lean convention; same instances
-- source:
--   Kempa–Kociumaka, A Complete Characterization of Central String Queries in Compact Space, STOC 2027 submission (manuscript sha256 dea2f74f66f1bd686c8e3c6d4e11f36643253c3c86a04fc5faa1c3ac1c96f346), Lemma 8.8, p.146 (PDF p.147)

import Mathlib
import Definitions.Def_CentralStrQ_LCPProfile

set_option autoImplicit false

namespace CentralStrQ

/-- Kempa–Kociumaka, *A Complete Characterization of Central String Queries in Compact Space*, STOC 2027 submission (manuscript sha256 dea2f74f…c96f346), Lemma 8.8, p.146 (PDF p.147): "Let W[1..m] be a sequence of strings, and let A[1..m) be a
sequence of nonnegative integers. Let i ∈ [1..m] and p ∈ [0..|W[i]|) be such that
h = prefix-special-pred_W(i, p + 1) ≠ −∞. Then profile_{A,W}(i)[p + 1] =
min{profile_{A,W}(y)[p] : y ∈ (h..i] and W[y] has prefix W[i][1..p]}."

**Formalization Note.** The minimum is stated with `IsLeast`: the value is attained by some `y`
in the set and is at most every member (the set contains `y = i`). -/
theorem lemma_8_8 {α : Type} [DecidableEq α] (W : List (List α)) (A : List ℕ)
    (hA : A.length = W.length - 1) (i p : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ W.length)
    (hp : p < (strAt W i).length) (h : ℕ) (hh : prefixSpecialPred W i (p + 1) = (h : WithBot ℕ)) :
    IsLeast {v : ℕ | ∃ y : ℕ, h < y ∧ y ≤ i ∧ (strAt W i).take p <+: strAt W y ∧
      v = profile A W y p} (profile A W i (p + 1)) := by sorry

end CentralStrQ
