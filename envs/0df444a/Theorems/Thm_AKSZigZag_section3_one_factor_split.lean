-- Prove2me | Theorems.Thm_AKSZigZag_section3_one_factor_split
-- name    : AKSZigZag.section3_one_factor_split
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:18:50.303285+00:00
-- url     : https://prove2.me/theorems/3e12df2e-402a-4e1f-88f2-68d7aaaaaf9f
-- title:
--   §3, p.4 — a bipartite graph of maximum valency $\le c$ splits into $c$ one-factors
-- statement:
--   Let $G$ be a finite bipartite graph in which every vertex has at most $c$ incident edges. Then the edge set of $G$ is the disjoint union of $c$ matchings $F_1,\dots,F_c$, some possibly empty.
--
--   In §3 each one-factor of the expander becomes one parallel step of comparators, so the halver has depth $c$.
--
--   Differences from the source:
--   - reading: one-factors F1,...,Fc → matchings (possibly empty); reason: the §2 expanders need not be regular, so perfect matchings cannot be meant
--   - generalization: the expander graph fitted to A and B → any finite bipartite graph of maximum valency ≤ c; reason: the splitting uses only the valency bound; the expander is one such graph
-- source:
--   Ajtai, Komlós, Szemerédi, An O(n log n) Sorting Network, STOC 1983, doi:10.1145/800061.808726, §3, p.4 ("Split the graph into c one-factors F1,...,Fc")

import Mathlib
import Definitions.Def_AKSZigZag_IsExpander

namespace AKSZigZag

/-- **Splitting into one-factors** (AKS, STOC 1983, doi:10.1145/800061.808726, §3, p.4): "Split
the graph into c one-factors F1,...,Fc." A finite bipartite graph in which every vertex has at
most `c` incident edges is the disjoint union of `c` matchings.

**Formalization Note.** "One-factor" is read as *matching*: the §2 expanders need not be
regular, so perfect matchings cannot be meant. Some `F k` may be empty. -/
theorem section3_one_factor_split {p q : ℕ} (E : Finset (Fin p × Fin q)) (c : ℕ)
    (hE : MaxValencyLE E c) :
    ∃ F : Fin c → Finset (Fin p × Fin q), (∀ k, IsMatching (F k)) ∧
      (∀ k l, k ≠ l → Disjoint (F k) (F l)) ∧ Finset.univ.biUnion F = E := by sorry

end AKSZigZag
