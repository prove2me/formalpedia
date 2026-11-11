-- Prove2me | Theorems.Thm_DynApproxIdx_Main_fact_7_6
-- name    : DynApproxIdx.Main.fact_7_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:51:22.308879+00:00
-- url     : https://prove2.me/theorems/03d4b499-ce62-4a28-a92c-001d2940e42d
-- title:
--   Fact 7.6 — a common last or first character does not change the edit distance
-- statement:
--   For strings $A,B$ and a character $c$, appending $c$ to both or prepending $c$ to both leaves the edit distance unchanged:
--   $$\delta_E(Ac,Bc)=\delta_E(A,B)=\delta_E(cA,cB).$$
--   Here $\delta_E$ is the edit distance (minimum number of character insertions, deletions and substitutions). The fact is used in the proof of Lemma 7.8 to split an alignment at exactly matched characters.
--
--   Differences from the source:
--
--   - encoding: strings over the integer alphabet Σ, 0-based positions; δ_E the minimum number of insertions, deletions and substitutions → List ℕ; PMEdits.Main.ed, the minimum cost of an alignment-graph path from (0,0) to (|U|,|V|); reason: the standard bijection between edit sequences and alignment-graph paths; same values
-- source:
--   Charalampopoulos, Ellert, Radoszewski, Dynamic Approximate Text Indexing, STOC 2027 submission (manuscript sha256 7f902057…), p. 32 (PDF 34), Fact 7.6

import Mathlib
import Definitions.Def_PMEdits_Main_Strings

namespace DynApproxIdx.Main

open PMEdits.Main

/-- **Fact 7.6** (Charalampopoulos, Ellert, Radoszewski, *Dynamic Approximate Text Indexing*, STOC
2027 submission, p. 32 (PDF 34)). For any two strings `A` and `B` and character `c`,
`δ_E(Ac, Bc) = δ_E(A, B) = δ_E(cA, cB)`. -/
theorem fact_7_6 (A B : List ℕ) (c : ℕ) :
    ed (A ++ [c]) (B ++ [c]) = ed A B ∧ ed A B = ed (c :: A) (c :: B) := by sorry

end DynApproxIdx.Main
