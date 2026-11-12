-- Prove2me | Theorems.Thm_BFFPyramidal_lemma_IV
-- name    : BFFPyramidal.lemma_IV
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-13T18:27:56.887787+00:00
-- url     : https://prove2.me/theorems/d97441cb-f831-4295-b4be-f398d4a3f7d2
-- title:
--   Lower bound for the size of a union of cosets
-- statement:
--   **Lemma IV.** Let $G$ be a pyramidal group, let $K_1,\dots,K_t$ be subgroups of $G$ and $a_1,\dots,a_t \in G$ arbitrary elements. Then
--   $$ \left| \bigcup_{i=1}^{t} a_iK_i \right| \;\ge\; \mu\!\left(D(R)\right), \qquad R = \{\, |K_i| : 1 \le i \le t \,\}, $$
--   where $D$ is the divisor closure and $\mu$ the totient measure.
--
--   The cosets are *not* assumed disjoint: this is a general lower bound on the size of a union of cosets in a pyramidal group, sensitive to the orders of the subgroups rather than merely to their number. It is the step that makes the multiplicity bound possible, since the conclusion of the main theorem counts subgroups of equal order.
--
--   **Formalization note.** The union is a `Set G` and its size is `Set.ncard`. $R$ is the image of the order function over all indices, so repeated orders are collapsed — $R$ is a set, not a multiset. The bound holds for every choice of coset representatives, including $t = 0$, where both sides are $0$.
-- source:
--   Berger--Felzenbaum--Fraenkel 1987, Remark on the multiplicity of a partition of a group into cosets, Fund. Math. 128 (1987) 139-144, https://doi.org/10.4064/fm-128-3-139-144, p. 141, Lemma IV and eqs. (15)-(16)

import Mathlib
import Definitions.Def_BFFPyramidal_pyramidal
import Definitions.Def_BFFPyramidal_arithmetic
open Pointwise

namespace BFFPyramidal

theorem lemma_IV {G : Type*} [Group G] [Finite G] (hG : IsPyramidal G)
    {t : ℕ} (K : Fin t → Subgroup G) (a : Fin t → G) :
    muMeasure (divisorClosure (Finset.image (fun i => Nat.card (K i)) Finset.univ))
      ≤ (⋃ i, (a i) • (K i : Set G)).ncard := by
  sorry

end BFFPyramidal
