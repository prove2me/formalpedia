-- Prove2me | Theorems.Thm_BalancedKneser_proposition_4_1
-- name    : BalancedKneser.proposition_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:47:46.796015+00:00
-- url     : https://prove2.me/theorems/65acd375-fdd0-4271-a842-43afbe17e8fc
-- title:
--   Proposition 4.1 (Rook generators) — $N(G_{n,3})$ is 6-connected and $H_7$ is spanned by rook cycles
-- statement:
--   Let $n\ge5$. Then:
--
--   1. the neighborhood complex $N(G_{n,3})$ is $6$-connected;
--   2. $H_7(N(G_{n,3});\mathbb F_2)$ is spanned by the **rook cycles**: number a $3\times3$ array of cells $D$ by $1,\dots,9$, let $A_i$ be the four other cells in the row or column of $i$, place $D$ in $[2n]$ and adjoin a fixed $(n-4)$-set $I$ disjoint from $D$; the rook cycle is the boundary of the eight-simplex on the nine labels $I\cup A_i$, and the cycles of the complemented configurations are included.
--
--   With Lemmas 3.1 and 4.2 this gives $\chi(G_{n,3})\ge10$ for $n\ge5$.
--
--   **Formalization Note** "Spanned by the rook cycles" is stated as: the images of $H_7(N(G_{n,3})[L];\mathbb F_2)$, over all rook label families $L$ (plain and complemented), span $H_7(N(G_{n,3});\mathbb F_2)$. Homology is singular homology of realizations, and $6$-connected includes nonemptiness.
--
--   Differences from the source:
--   - generalization: N(G_{n,3}) is 6-connected (printed definition, which does not require nonemptiness) → IsConnectedUpTo … 6, which also asserts that |N(G_{n,3})| is nonempty; reason: the Lean conclusion implies the printed one, and nonemptiness is true for n ≥ 5; it keeps the mission's single (corrected) connectivity definition
--   - encoding: H₇(−; F₂) is spanned by the rook cycles → the images of H₇ of the induced subcomplexes N(G_{n,3})[L] over the rook label families L span H₇(N(G_{n,3}); F₂); reason: an induced subcomplex on nine vertices has nonzero H₇ only if it is the boundary of the simplex on them, and then H₇ is spanned by that cycle; every proper subfamily of L is a face (p.8, (4.1)), so the image is exactly the span of the rook cycle
--   - encoding: the 3 × 3 array numbered 1, …, 9 row by row, placed as D ⊆ [2n] → rookA on Fin 9 (cell i is the source's cell i + 1) transported by an injection e : Fin 9 ↪ Fin (2n); reason: every placement of the array on a nine-point set arises from some bijection
--   - encoding: simplicial homology of the complex → singular homology of its geometric realization (Hatcher.Singular.H); reason: the two agree for finite simplicial complexes; same groups
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, Proposition 4.1, p.8 (PDF p.10); configurations, p.8

import Mathlib
import Definitions.Def_Hatcher_SingularHomology
import Definitions.Def_BalancedKneser_KG
import Definitions.Def_TreeCoverLB_realization
import Definitions.Def_BalancedKneser_inclusionMap
import Definitions.Def_BalancedKneser_nbhdComplex
import Definitions.Def_BalancedKneser_IsConnectedUpTo
import Definitions.Def_BalancedKneser_rookLabelSets

namespace BalancedKneser

/-- **Proposition 4.1 (Rook generators)** (Alipour–Jafari, arXiv:2611.04486v1, p.8 (PDF p.10)):
"For n ≥ 5, the complex N(G_{n,3}) is 6-connected, and its H7(−; F2) is spanned by the rook
cycles just described."

The rook cycle of a configuration with label set `L` (nine `n`-sets, see `rookLabelSets`; plain
and complemented configurations) is the boundary of the simplex on `L`. "Spanned by the rook
cycles" is: the images of `H₇` of the induced subcomplexes `N(G_{n,3})[L]`, over all
configurations, span `H₇(|N(G_{n,3})|; F₂)`.

Formalization Note: homology is singular homology of realizations; `IsConnectedUpTo` includes
nonemptiness. -/
theorem proposition_4_1 (n : ℕ) (hn : 5 ≤ n) :
    IsConnectedUpTo (TreeCoverLB.realization (nbhdComplex (Gnr n 3))) 6 ∧
    (⨆ (L : Finset (KSet (2 * n) n)) (_ : L ∈ rookLabelSets n),
      LinearMap.range (Hatcher.Singular.map (ZMod 2) 7
        (inclusionMap (restrict_subset (nbhdComplex (Gnr n 3)) L))).hom) = ⊤ := by sorry

end BalancedKneser
