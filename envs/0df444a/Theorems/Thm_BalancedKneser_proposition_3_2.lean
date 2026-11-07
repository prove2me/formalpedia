-- Prove2me | Theorems.Thm_BalancedKneser_proposition_3_2
-- name    : BalancedKneser.proposition_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:47:20.5458+00:00
-- url     : https://prove2.me/theorems/e6f65845-fb3f-4e59-84b1-020c7004dea5
-- title:
--   Proposition 3.2 (Pentagon generators) — $N(G_{n,2})$ is 2-connected and $H_3$ is spanned by pentagon cycles
-- statement:
--   Let $n\ge3$. Then:
--
--   1. the neighborhood complex $N(G_{n,2})$ is $2$-connected;
--   2. $H_3(N(G_{n,2});\mathbb F_2)$ is spanned by the **pentagon cycles**: for disjoint $I,D\subseteq[2n]$ with $|I|=n-2$, $|D|=5$ and a pentagon on $D$ with neighbor pairs $A_1,\dots,A_5$, the cycle $z_{I,D}$ is the boundary of the four-simplex on the five labels $I\cup A_i$; the cycles of the complemented configurations (the five complements $[2n]\setminus(I\cup A_i)$) are included.
--
--   Every proper subfamily of the five labels of a configuration is a face of $N(G_{n,2})$, so $z_{I,D}$ is a $3$-cycle supported on those labels, and the span of its class is the image of $H_3$ of the induced subcomplex on the labels. With Lemmas 3.1 and 3.3 this gives $\chi(G_{n,2})\ge6$.
--
--   **Formalization Note** "Spanned by the pentagon cycles" is stated as: the images of $H_3(N(G_{n,2})[L];\mathbb F_2)$, over all pentagon label families $L$ (plain and complemented), span $H_3(N(G_{n,2});\mathbb F_2)$. Homology is singular homology of realizations, and $2$-connected includes nonemptiness.
--
--   Differences from the source:
--   - generalization: N(G_{n,2}) is 2-connected (printed definition, which does not require nonemptiness) → IsConnectedUpTo … 2, which also asserts that |N(G_{n,2})| is nonempty; reason: the Lean conclusion implies the printed one, and nonemptiness is true for n ≥ 3; it keeps the mission's single (corrected) connectivity definition
--   - encoding: H₃(−; F₂) is spanned by the pentagon cycles z_{I,D} → the images of H₃ of the induced subcomplexes N(G_{n,2})[L] over the pentagon label families L span H₃(N(G_{n,2}); F₂); reason: an induced subcomplex on five vertices has nonzero H₃ only if it is the boundary of the simplex on them, and then H₃ is spanned by that boundary cycle; every proper subfamily of L is a face (p.6), so the image is exactly the span of [z_{I,D}]
--   - encoding: a pentagon on a five-point set D ⊆ [2n] → pentA on Fin 5 transported by an injection e : Fin 5 ↪ Fin (2n) with image D; reason: every pentagon on D arises from some bijection Fin 5 ≃ D
--   - encoding: simplicial homology of the complex → singular homology of its geometric realization (Hatcher.Singular.H); reason: the two agree for finite simplicial complexes; same groups
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, Proposition 3.2, p.6 (PDF p.8); configurations, p.6

import Mathlib
import Definitions.Def_Hatcher_SingularHomology
import Definitions.Def_BalancedKneser_KG
import Definitions.Def_TreeCoverLB_realization
import Definitions.Def_BalancedKneser_inclusionMap
import Definitions.Def_BalancedKneser_nbhdComplex
import Definitions.Def_BalancedKneser_IsConnectedUpTo
import Definitions.Def_BalancedKneser_pentagonLabelSets

namespace BalancedKneser

/-- **Proposition 3.2 (Pentagon generators)** (Alipour–Jafari, arXiv:2611.04486v1, p.6
(PDF p.8)): "For n ≥ 3, the complex N(G_{n,2}) is 2-connected, and its H3(−; F2) is spanned by
the pentagon cycles just described."

The pentagon cycle `z_{I,D}` of a configuration with label set `L` (five `n`-sets, see
`pentagonLabelSets`; plain and complemented configurations) is the boundary of the simplex on
`L`. Every class supported on `L` lies in the image of `H₃` of the induced subcomplex
`N(G_{n,2})[L]`, and that image is spanned by `[z_{I,D}]`; so "spanned by the pentagon cycles"
is: these images, over all configurations, span `H₃(|N(G_{n,2})|; F₂)`.

Formalization Note: homology is singular homology of realizations; `IsConnectedUpTo` includes
nonemptiness. -/
theorem proposition_3_2 (n : ℕ) (hn : 3 ≤ n) :
    IsConnectedUpTo (TreeCoverLB.realization (nbhdComplex (Gnr n 2))) 2 ∧
    (⨆ (L : Finset (KSet (2 * n) n)) (_ : L ∈ pentagonLabelSets n),
      LinearMap.range (Hatcher.Singular.map (ZMod 2) 3
        (inclusionMap (restrict_subset (nbhdComplex (Gnr n 2)) L))).hom) = ⊤ := by sorry

end BalancedKneser
