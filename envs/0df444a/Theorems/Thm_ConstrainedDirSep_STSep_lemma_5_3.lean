-- Prove2me | Theorems.Thm_ConstrainedDirSep_STSep_lemma_5_3
-- name    : ConstrainedDirSep.STSep.lemma_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:08:04.706432+00:00
-- url     : https://prove2.me/theorems/b279fab1-2dd0-4d97-90b9-2295e9c63117
-- title:
--   Lemma 5.3 — vertex splitting: S separates s from t iff {e_v : v ∈ S} is an s–t arc cut of the split graph
-- statement:
--   Let $D$ be a loopless digraph on $\{0,\dots,n-1\}$ with distinct terminals $s,t$, let $G$ be its split graph (every nonterminal $v$ split into $v^-\to v^+$ by the split arc $e_v$, every arc $uv$ of $D$ becoming $u^+v^-$, terminals unsplit), and for $S\subseteq V(D)\setminus\{s,t\}$ let $Z_S=\{e_v: v\in S\}$. Then
--   $$S \text{ is an } s\text{–}t \text{ vertex separator in } D \iff Z_S \text{ is an } s\text{–}t \text{ arc cut in } G,$$
--   and $S$ is an inclusion-minimal $s$–$t$ vertex separator if and only if $Z_S$ is an inclusion-minimal $s$–$t$ arc cut.
--
--   This translates vertex separators into arc cuts, to which directed flow augmentation (Theorem 5.4) applies.
--
--   Differences from the source:
--   - encoding: split graph vertices v⁻, v⁺ with s± = s, t± = t → two copies of {0, …, n−1} (v⁻ the first copy, v⁺ the second for a nonterminal, the terminals in the first copy), arcs an indexed family; reason: the two unused second copies of s and t are isolated and change no walk or cut.
-- source:
--   Olkowski, Ramanujan, Constrained Directed Separation: Algorithms and Classifications, STOC 2027 submission (manuscript sha256 4dd06c29…), p. 19 (PDF 22), Lemma 5.3 (proof pp. 42–43, PDF 45–46)

import Mathlib
import Definitions.Def_ConstrainedDirSep_STSep_Separator
import Definitions.Def_ConstrainedDirSep_STSep_Multigraph

namespace ConstrainedDirSep.STSep

/-- Olkowski, Ramanujan, *Constrained Directed Separation*, STOC 2027 submission (manuscript
sha256 4dd06c29…), p. 19 (PDF 22), Lemma 5.3: for `S ⊆ V(D) \ {s, t}` and `Z_S = {e_v : v ∈ S}`,
`S` is an s–t vertex separator in `D` iff `Z_S` is an s–t arc cut in the split graph `G`, and
inclusion-minimality is preserved in both directions. -/
theorem lemma_5_3 {n : ℕ} (D : Digraph (Fin n)) (hD : Loopless D) (s t : Fin n) (hst : s ≠ t)
    (S : Finset (Fin n)) (hs : s ∉ S) (ht : t ∉ S) :
    (IsSTSeparator D s t (S : Set (Fin n)) ↔
      (splitGraph D s t).toMultigraph.IsArcCut (Sum.inl s) (Sum.inl t) (splitArcsOf D s t S)) ∧
    (IsMinimalSTSeparator D s t (S : Set (Fin n)) ↔
      (splitGraph D s t).toMultigraph.IsMinimalArcCut (Sum.inl s) (Sum.inl t)
        (splitArcsOf D s t S)) := by sorry

end ConstrainedDirSep.STSep
