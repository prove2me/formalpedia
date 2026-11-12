-- Prove2me | Theorems.Thm_BFFPyramidal_lemma_I
-- name    : BFFPyramidal.lemma_I
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-13T18:26:01.74599+00:00
-- url     : https://prove2.me/theorems/2e451e31-3c86-4925-be49-4554285c1d58
-- title:
--   Intersection of two cosets
-- statement:
--   **Lemma I.** Let $K$ and $L$ be subgroups of a group $G$ and let $a, b \in G$. Then the intersection $aK \cap bL$ is either empty or a coset of $K \cap L$. In particular, when it is nonempty,
--   $$ |aK \cap bL| \;=\; |K \cap L| . $$
--
--   This is the basic combinatorial fact underlying every counting argument about coset partitions.
--
--   **Formalization note.** The statement is a disjunction: either the intersection of the two cosets, as sets, is empty, or there exists $c \in G$ with $aK \cap bL = c(K \cap L)$. The cardinality assertion follows, since a coset of $K \cap L$ has exactly $|K \cap L|$ elements. Cosets are pointwise scalar multiples of the underlying sets (`•` on `Set G`, requiring `open Pointwise`), and $K \cap L$ is the lattice meet `K ⊓ L` of subgroups. No finiteness is needed.
-- source:
--   Berger--Felzenbaum--Fraenkel 1987, Remark on the multiplicity of a partition of a group into cosets, Fund. Math. 128 (1987) 139-144, https://doi.org/10.4064/fm-128-3-139-144, p. 140, Lemma I and eq. (5)

import Mathlib
open Pointwise

namespace BFFPyramidal

theorem lemma_I {G : Type*} [Group G] (K L : Subgroup G) (a b : G) :
    (a • (K : Set G)) ∩ (b • (L : Set G)) = ∅ ∨
      ∃ c : G, (a • (K : Set G)) ∩ (b • (L : Set G)) = c • ((K ⊓ L : Subgroup G) : Set G) := by
  sorry

end BFFPyramidal
