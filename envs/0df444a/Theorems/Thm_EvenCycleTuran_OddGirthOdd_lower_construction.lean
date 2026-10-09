-- Prove2me | Theorems.Thm_EvenCycleTuran_OddGirthOdd_lower_construction
-- name    : EvenCycleTuran.OddGirthOdd.lower_construction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:25:06.108248+00:00
-- url     : https://prove2.me/theorems/b107191d-7706-4d9e-bc7d-d1af62bf48cf
-- title:
--   Proof of Theorem 18, p. 28 — replacing the hyperedges of a girth-(2k+2) hypergraph by C_{2l+1}'s
-- statement:
--   Let $k > l \ge 2$. Let $\mathcal H$ be a $(2l+1)$-uniform hypergraph on $n$ vertices of girth at least $2k+2$, and let $G$ be the graph obtained by replacing every hyperedge of $\mathcal H$ by a cycle $C_{2l+1}$ through its $2l+1$ vertices (in any chosen cyclic order). Then:
--
--   1. $G$ contains no cycle of length $a$ for any $3 \le a \le 2k+1$ with $a \ne 2l+1$; in particular $G$ is $\mathcal C_{2l} \cup \{C_{2k+1}\}$-free;
--   2. the number of copies of $C_{2l+1}$ in $G$ is at least the number of hyperedges:
--
--   $$\mathcal N(C_{2l+1}, G) \ge |E(\mathcal H)|.$$
--
--   Combined with Theorem 29 (for $r = 2l+1$, $s = 2k+2$), this gives the lower bound $\Omega(n^{1+1/(2k+2)})$ of Theorem 18.
--
--   **Formalization Note** The cyclic order of each hyperedge is given as an injective map $\sigma_e : \{0, \dots, 2l\} \to V$ whose image is the hyperedge $e$; the cycle has edges $\sigma_e(i)\sigma_e(i+1)$ (indices mod $2l+1$). The page states only the construction for Theorem 18; the freeness claim is the one stated for Theorem 17 on p. 27, with $2k$ replaced by $2k+1$.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 28, proof of Theorem 18, lower bound (cf. p. 27, proof of Theorem 17)

import Mathlib
import Definitions.Def_EvenCycleTuran_OddGirthOdd_Setting

namespace EvenCycleTuran.OddGirthOdd

/-- The lower-bound construction in the proof of Theorem 18, p. 28: replacing each hyperedge of a
(2l+1)-uniform hypergraph of girth at least 2k+2 by a C_{2l+1} gives a graph with no cycle of
length 3, …, 2k+1 other than 2l+1, and at least one C_{2l+1} per hyperedge. -/
theorem lower_construction (k l : ℕ) (hl : 2 ≤ l) (hkl : l < k)
    (n : ℕ) (H : Hypergraph (Fin n))
    (huniform : IsUniform H (2 * l + 1)) (hgirth : GirthGe H (2 * k + 2))
    (σ : (e : {e // e ∈ H}) → Fin (2 * l + 1) ↪ Fin n)
    (hσ : ∀ e, Finset.univ.map (σ e) = e.val) :
    CycleFree (Set.Icc 3 (2 * k + 1) \ {2 * l + 1})
      (replaceEdges H (2 * l + 1) σ) ∧
    H.card ≤ (replaceEdges H (2 * l + 1) σ).copyCount
      (SimpleGraph.cycleGraph (2 * l + 1)) := by sorry

end EvenCycleTuran.OddGirthOdd
