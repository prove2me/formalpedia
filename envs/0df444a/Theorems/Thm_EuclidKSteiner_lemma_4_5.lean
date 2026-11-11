-- Prove2me | Theorems.Thm_EuclidKSteiner_lemma_4_5
-- name    : EuclidKSteiner.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:18:47.229384+00:00
-- url     : https://prove2.me/theorems/9ce360ca-3453-4f0b-b34a-e57c1678d6f7
-- title:
--   Lemma 4.5 — the recurrence (4.3)–(4.4) computes exactly the full families $D[u,i,v]$
-- statement:
--   Work in the graph setting and fix a template $T$. For every vertex $u$ of $T$, every $0\le i\le\mathrm{child}(u)$ and every host $v$, the family obtained from the base case (4.3) and the transition (4.4) equals the full table entry $D[u,i,v]$, the set of pairs (terminal-image set, cost) of all realizations of the partial template $T_{u,i}$ that map $u$ to $v$.
--
--   This is the correctness of the uncompressed dynamic program.
--
--   Differences from the source:
--   - generalization: a fixed augmented tree template (Definition 4.2) → every well-formed code (balanced word, one role per vertex), without conditions 1–4 of Definition 4.2; reason: the recurrence and its correctness use none of those conditions; templates are well-formed codes
--   - encoding: the recurrence (4.3)–(4.4) → DrecF with fuel equal to the number of template vertices; reason: the fuel exceeds the depth of the tree, so it never runs out
-- source:
--   Bhore, Kisfaludi-Bak, Marx, Odak, Parameterized Tractability of Euclidean k-Steiner Tree, STOC 2027 submission (manuscript sha256 75361687…), Lemma 4.5, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_EuclidKSteiner_Template

namespace EuclidKSteiner

/-- **Lemma 4.5.** Bhore, Kisfaludi-Bak, Marx, Odak, *Parameterized Tractability of Euclidean
k-Steiner Tree*, STOC 2027 submission (manuscript sha256 75361687…), Lemma 4.5, p.18 (PDF p.20):
"Equations (4.3) and (4.4) give exactly the full families defined above."

For every well-formed template `T`, vertex `u`, `0 ≤ i ≤ child(u)` and host `v`, the family computed
by the base case (4.3) and the transition (4.4) equals the full table entry `D[u, i, v]`: the set of
pairs (terminal-image set, cost) of all realizations of the partial template `T_{u,i}` mapping `u`
to `v`.

**Formalization Note** Stated for every well-formed code; the conditions 1–4 of Definition 4.2 are not
used by the recurrence. The recurrence is evaluated with fuel equal to the number of vertices. -/
theorem lemma_4_5 {V : Type*} [Fintype V] [DecidableEq V] (S : GraphSetting V) (T : Template)
    (hT : T.WellFormed) (u : ℕ) (hu : u < T.size) (i : ℕ) (hi : i ≤ T.nch u) (v : V) :
    S.Drec T u i v = S.Dfull T u i v := by sorry

end EuclidKSteiner
