-- Prove2me | Theorems.Thm_ForestPersuasion_Symmetric_recursion_7
-- name    : ForestPersuasion.Symmetric.recursion_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:26:44.8652+00:00
-- url     : https://prove2.me/theorems/b5ceaf8d-da49-4b9c-9d07-f90036f9c2e2
-- title:
--   §5, recursion (7) — subtree minima and the N identity
-- statement:
--   Fix a valid forest persuasion model and arbitrary real dual coefficients $\gamma,\delta$. Let $F$ be the minimum of the original subtree expression. At every leaf $j$,
--   $$F(j,0,l)=(1-\tau_l)\gamma^j_{0,l}.$$
--   For every receiver $j$, every $0\le\kappa<d_j$, and every grid index $l$, let $H(j,\kappa,l)$ be the minimum over child choices with $\sum_i(\kappa_i+\mathbf1_{\tau_{l_i}\ge t_i})=\kappa$ of $\sum_i(F(i,\kappa_i,l_i)+(\tau_l-\tau_{l_i})\delta^{j,i}_{\kappa_i,l_i})$. Then
--   $$F(j,\kappa,l)=(1-\tau_l)\gamma^j_{\kappa,l}+H(j,\kappa,l),\qquad H(j,\kappa,l)=N^j_{s(j),\kappa}.$$
--   The table $N$ has the stated zero/positive-infinity base and count-convolution recursion. These identities concern the independently defined minimum $F$ and include the whole child-count identity used for the dual separation calculation.
--
--   Differences from the source:
--   - encoding: receivers 1,...,n and a directed forest → Fin n and an acyclic optional-parent map; reason: a relabelling of the same finite rooted forests; receiver i observes every coordinate in its reflexive descendant set
--   - generalization: n receivers with n implicitly positive → n may also be zero; reason: with no receivers all vertex-indexed identities are vacuous; every positive-size instance is retained
--   - encoding: indices l=0,...,m with increasing distinct values τ_l → the subtype of distinct grid values, one coordinate per receiver; reason: the increasing enumeration tau is supplied and gives a bijective reindexing of the same grid
--   - encoding: free dual entries for edges and 0≤κ<d_i → real arrays extended to natural κ and all vertex pairs; reason: all expressions read only source-domain entries, and every finite source array has such an extension
--   - encoding: constrained minima, including +∞ for impossible counts → EReal infima of finite real candidate sets, with empty value +∞; reason: the same minimum when feasible, no default zero on empty sets; neither -∞ nor indeterminate infinity arithmetic occurs
--   - encoding: an arbitrary ordering i_1,...,i_s of each node's children → increasing vertex order, with a fallback only beyond the last child; reason: this is one allowed ordering; the identities evaluate N only through s(j), never the fallback
--   - generalization: recursion (7) is stated for non-leaf vertices, with a separate leaf formula → the recursive and N identities also apply to leaves at the sole allowed count κ=0; reason: the empty child choice has count zero and sum zero, and N at zero children and count zero is zero; the leaf identity and all non-leaf instances are retained
-- source:
--   Konstantin Zabarnyi, Designing Information in a Forest: Algorithmic Aspects, STOC 2027 submission #271 (October 2026; PDF dated November 2, 2026), §5, recursion (7), leaf base and N identity, PDF pp. 14–15 (printed pp. 13–14). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/271.pdf

import Mathlib
import Definitions.Def_ForestPersuasion_Symmetric_DP

open scoped NNReal ENNReal

namespace ForestPersuasion.Symmetric

/-- §5, recursion (7) and the N identity (PDF pp. 14–15).
F is the independently defined minimum of subtreeCost, not the recursive expression.
All dual coefficients are free real numbers. -/
theorem recursion_7 {n : ℕ} (I : Model n) (hI : I.Valid) (C : DualCoefficients I) :
    (∀ (j : Fin n) (q : Grid I), I.hierarchy.children j = ∅ →
      F I C j 0 q = (((1 - q.val) * C.gamma j 0 q : ℝ) : EReal)) ∧
    (∀ (j : Fin n) (κ : ℕ) (q : Grid I), κ < (I.hierarchy.descendants j).card →
      F I C j κ q = (((1 - q.val) * C.gamma j κ q : ℝ) : EReal) +
        childrenMinimum I C j κ q ∧
      childrenMinimum I C j κ q = N I C j q (childrenList I j).length κ) := by sorry

end ForestPersuasion.Symmetric
