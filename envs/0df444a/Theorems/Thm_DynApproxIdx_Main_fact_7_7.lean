-- Prove2me | Theorems.Thm_DynApproxIdx_Main_fact_7_7
-- name    : DynApproxIdx.Main.fact_7_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:52:16.538575+00:00
-- url     : https://prove2.me/theorems/0e5eefe2-8307-4d3b-bf2a-de4d92c1ecd6
-- title:
--   Fact 7.7 — an alignment of cost d matches positions at offset at most d
-- statement:
--   Let $X,Y$ be strings and $A$ an alignment of $X$ and $Y$ of cost $d$. If $A(i)=j$, that is, $X[i]$ and $Y[j]$ are both preserved and matched by the alignment, then
--   $$|j-i|\le d.$$
--   The fact bounds how far an exactly matched copy of $Q$ can move under an alignment of small cost, which the proof of Claim 7.9 uses.
--
--   Differences from the source:
--
--   - encoding: strings over the integer alphabet Σ, 0-based positions; δ_E the minimum number of insertions, deletions and substitutions → List ℕ; PMEdits.Main.ed, the minimum cost of an alignment-graph path from (0,0) to (|U|,|V|); reason: the standard bijection between edit sequences and alignment-graph paths; same values
--   - encoding: an alignment A of X and Y of cost d (§7.1: a partial map i ↦ j induced by a transformation with at most d edits) → a path A of the alignment graph from (0,0) to (|X|,|Y|) with alnCost = d; A(i) = j iff A takes the diagonal edge (i,j)→(i+1,j+1) and X[i] = Y[j] (AlignMap); reason: edit transformations and alignment-graph paths correspond with the same cost and the same preserved pairs; a transformation with a wasted substitution yields fewer pairs and a larger cost, so the path statement implies it
-- source:
--   Charalampopoulos, Ellert, Radoszewski, Dynamic Approximate Text Indexing, STOC 2027 submission (manuscript sha256 7f902057…), p. 32 (PDF 34), Fact 7.7

import Mathlib
import Definitions.Def_PMEdits_Main_Strings
import Definitions.Def_DynApproxIdx_Main_Strings

namespace DynApproxIdx.Main

open PMEdits.Main

/-- **Fact 7.7** (Charalampopoulos, Ellert, Radoszewski, *Dynamic Approximate Text Indexing*, STOC
2027 submission, p. 32 (PDF 34)). If an alignment `A` of two strings `X` and `Y` of cost `d`
satisfies `A(i) = j`, then `|j − i| ≤ d`. The alignment is a path of the alignment graph from
`(0, 0)` to `(|X|, |Y|)` of cost `d`, and `A(i) = j` means that it takes the diagonal edge
`(i, j) → (i+1, j+1)` with `X[i] = Y[j]`. -/
theorem fact_7_7 (X Y : List ℕ) (A : List (ℤ × ℤ)) (d : ℕ)
    (hA : IsAlignment 0 X.length 0 Y.length A) (hd : alnCost (chars X) (chars Y) A = d)
    (i j : ℤ) (hij : AlignMap X Y A i j) :
    |j - i| ≤ (d : ℤ) := by sorry

end DynApproxIdx.Main
