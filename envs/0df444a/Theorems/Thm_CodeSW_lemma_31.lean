-- Prove2me | Theorems.Thm_CodeSW_lemma_31
-- name    : CodeSW.lemma_31
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:26:02.702677+00:00
-- url     : https://prove2.me/theorems/faa12931-4b98-404d-9275-ae123f49658e
-- title:
--   Lemma 31 — weighted-coset inequality $\sum_{S\in a+L}w(S)\le Z_L$
-- statement:
--   **Weighted-coset inequality.** Let $L\subseteq\{0,1\}^c$ be a linear subspace, let $0\le r\le1$, and define $w(S)=r^{|S|}$ and $Z_L=\sum_{S\in L}w(S)$. Then for every $a\in\{0,1\}^c$,
--   $$\sum_{S\in a+L}w(S)\le Z_L.$$
--
--   A linear code has at least as much weight, under a weight that decays with Hamming weight, as any of its cosets. This controls the normalizing constants and the flow through a transition in the canonical paths argument.
--
--   Differences from the source:
--   - generalization: 0 < r ≤ 1 → 0 ≤ r ≤ 1; reason: the inequality also holds at r = 0, with 0⁰ = 1; every r in the source's range is covered
-- source:
--   Hangleiter, Ju, Vazirani, Code Swendsen-Wang Dynamics, arXiv:2510.08446 (manuscript sha256 4e4abb5e…), Lemma 31, p.37

import Definitions.Def_CodeSW_kerA
open Matrix

namespace CodeSW

open Classical in
/-- **Lemma 31 (Weighted-coset inequality).** Let `L ⊆ {0,1}^c` be a linear subspace, let
`0 ≤ r ≤ 1`, and define `w(S) = r^{|S|}` and `Z_L = ∑_{S∈L} w(S)`. Then, for every `a ∈ {0,1}^c`,
`∑_{S ∈ a+L} w(S) ≤ Z_L` (Hangleiter, Ju, Vazirani, *Code Swendsen-Wang Dynamics*,
arXiv:2510.08446, manuscript sha256 4e4abb5e…, Lemma 31, p.37).

**Formalization Note** `|S|` is the Hamming weight; `S ∈ a + L` iff `S − a ∈ L`. The page assumes
`0 < r ≤ 1`; `r = 0` is included (with `0^0 = 1`). -/
theorem lemma_31 {c : ℕ} (L : Submodule (ZMod 2) (Fin c → ZMod 2)) (r : ℝ) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (a : Fin c → ZMod 2) :
    ∑ S ∈ Finset.univ.filter (fun S : Fin c → ZMod 2 => S - a ∈ L), r ^ hammingWeight S ≤
      ∑ S ∈ Finset.univ.filter (fun S : Fin c → ZMod 2 => S ∈ L), r ^ hammingWeight S := by sorry

end CodeSW
