-- Prove2me | Theorems.Thm_CallCountPOPBR_Supplement_theorem_7_8
-- name    : CallCountPOPBR.Supplement.theorem_7_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:07:58.171608+00:00
-- url     : https://prove2.me/theorems/c7d457ee-3ca6-49ff-b5b7-c3cc829e52c0
-- title:
--   Theorem 7.8 — maximum-growth uniqueness
-- statement:
--   For every full-binary decreasing specification with base set $\{0\}$, the following are equivalent:
--
--   1. its invocation count is
--
--      $$
--      c_n=2^{n+1}-1\qquad\text{for every }n\ge0;
--      $$
--
--   2. for every $n\ge1$, both immediate recursive arguments are $n-1$.
--
--   Thus the maximal-growth sequence exactly characterises the specification that doubles the preceding subtree at every input.
--
--   Differences from the source:
--   - encoding: an unordered child pair with repetition → an element of $\operatorname{Sym}^2(\operatorname{Fin} n)$ equal to $\{n-1,n-1\}$; reason: this is the direct finite-index representation of both recursive arguments
--   - encoding: $2^{n+1}-1$ → natural-number exponentiation and subtraction; reason: the subtraction is exact because $2^{n+1}\ge1$
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884…), Theorem 7.8, pp.13–14

import Mathlib
import Definitions.Def_CallCountPOPBR_Supplement_BinSpec

set_option autoImplicit false

namespace CallCountPOPBR.Supplement

/-- **Theorem 7.8 (Maximum-growth uniqueness).** Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…), Theorem 7.8, p.13: "In the full-binary model
with base set {0} (that is, β = 1), the following statements are equivalent: (i) c_n = 2^{n+1} − 1
for every n ≥ 0; (ii) at every input n ≥ 1, both immediate recursive arguments are n − 1."

For every full-binary specification `σ` with base set `{0}`: its call counts are `2^{n+1} − 1` for
all `n` iff its child pair at every `n ≥ 1` is `{n − 1, n − 1}`.

**Formalization Note.** `2^{n+1} − 1` is natural-number subtraction, exact since `2^{n+1} ≥ 1`. -/
theorem theorem_7_8 (σ : BinSpec 1) :
    (∀ n, σ.count n = 2 ^ (n + 1) - 1) ↔
      ∀ n (h : 1 ≤ n), σ n h = s((⟨n - 1, by omega⟩ : Fin n), (⟨n - 1, by omega⟩ : Fin n)) := by sorry

end CallCountPOPBR.Supplement
