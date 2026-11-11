-- Prove2me | Theorems.Thm_FTConnOracle_Main_observation_4_2
-- name    : FTConnOracle.Main.observation_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:36:08.210198+00:00
-- url     : https://prove2.me/theorems/e074e38c-cad3-40b0-a18c-1fac8f23e10b
-- title:
--   Observation 4.2 — when level i+1 has no surviving crossing edge, f_{i+1} − r_i estimates b within D
-- statement:
--   Let $n\ge2$, let $G$ be a graph on $[n]$, $M_1,M_2,\dots$ masks, $D\ge0$ and $i\ge0$, with $G_0=G$, $G_{i+1}=G_i\cap M_{i+1}$, and $M_{i+1}$ $D$-good for $G_i$. Let $F\subseteq E(G)$, $F_0=F$, $F_{i+1}=F_i\cap E(M_{i+1})$, let $S\subseteq[n]$, and set
--
--   $$b=|\delta_{G_i-F_i}(S)|,\qquad r_i=|\delta_{F_i\setminus F_{i+1}}(S)|,\qquad f_{i+1}=|\delta_{F_{i+1}}(S)|.$$
--
--   If $G_{i+1}-F_{i+1}$ has no edge crossing $S$, then
--
--   $$\big|\,b-(f_{i+1}-r_i)\,\big|\le D.$$
--
--   The quantities $r_i$ and $f_{i+1}$ are computable from $F$ and the masks alone, so this is the estimate behind Case 1 of the level decoder (Claim 4.5).
--
--   Differences from the source:
--   - generalization: the hierarchy of §4.3: masks M_1, …, M_L from the family M_n of Lemma 4.6, each M_{i+1} D-good for G_i, G_L = ∅, i < L, D = 2C n^{3/2}√(log n) → any masks M (i + 1) on [n], only M_{i+1} assumed D-good for G_i, any D ≥ 0 and any i ∈ ℕ; reason: the proof uses only the cut approximation (4.7) of M_{i+1} and F ⊆ E(G); the source's hierarchy is an instance
--   - encoding: masks M_1, M_2, … → M : ℕ → SimpleGraph (Fin n) with M (i + 1) = M_{i+1}; reason: indexing convention; M 0 is never read
-- source:
--   Parter, Tzalik, Deterministic Fault-Tolerant Connectivity Oracles with Subqadratic Space, STOC 2027 submission (manuscript sha256 168306b7…), p. 24 (PDF 26), Observation 4.2 (in the proof of Claim 4.5)

import Mathlib
import Definitions.Def_FTConnOracle_Main_Oracle
import Definitions.Def_FTConnOracle_Main_Mask

namespace FTConnOracle.Main

/-- Observation 4.2 (p. 24): with `G_i`, `F_i` the level graphs and level failure sets, `M_{i+1}`
`D`-good for `G_i`, and `F ⊆ E(G)`: if `G_{i+1} − F_{i+1}` has no edge crossing `S`, then
`|b − (f_{i+1} − r_i)| ≤ D`, where `b = |δ_{G_i − F_i}(S)|`, `r_i = |δ_{F_i ∖ F_{i+1}}(S)|` and
`f_{i+1} = |δ_{F_{i+1}}(S)|`. -/
theorem observation_4_2 {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n))
    (M : ℕ → SimpleGraph (Fin n)) (D : ℝ) (hD : 0 ≤ D) (i : ℕ)
    (hgood : IsDGood D (M (i + 1)) (levelGraph G M i)) (F : Finset (Sym2 (Fin n)))
    (hF : F ⊆ edges G) (S : Finset (Fin n))
    (hempty : delta (removeEdges (levelGraph G M (i + 1)) (levelFail F M (i + 1))) S = ∅) :
    |((delta (removeEdges (levelGraph G M i) (levelFail F M i)) S).card : ℝ) -
        (((cutEdges (levelFail F M (i + 1)) S).card : ℝ) -
          ((cutEdges (levelFail F M i \ levelFail F M (i + 1)) S).card : ℝ))| ≤ D := by sorry

end FTConnOracle.Main
