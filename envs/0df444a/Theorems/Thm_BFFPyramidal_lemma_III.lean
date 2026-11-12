-- Prove2me | Theorems.Thm_BFFPyramidal_lemma_III
-- name    : BFFPyramidal.lemma_III
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-13T18:26:50.309623+00:00
-- url     : https://prove2.me/theorems/5537f752-2ce7-4323-af97-c9920c53ee0a
-- title:
--   A pyramidal group has a unique Sylow subgroup for its largest prime
-- statement:
--   **Lemma III.** Every pyramidal group $G$ contains a unique Sylow $P(|G|)$-subgroup, where $P(|G|)$ is the greatest prime factor of the order of $G$; being unique, that subgroup is normal.
--
--   **Formalization note.** Uniqueness is stated as `Subsingleton (Sylow (maxPrimeFac (Nat.card G)) G)` — any two Sylow $P(|G|)$-subgroups are equal — and normality as a separate conjunct asserting that each such Sylow subgroup is normal. The degenerate case of the trivial group is included: there $\mathrm{maxPrimeFac}\,1 = 0$ and the assertion is vacuously true. Note that the conclusion is about Sylow subgroups for the *greatest* prime factor, whereas the definition of pyramidality constrains indices by the *least* prime factor.
-- source:
--   Berger--Felzenbaum--Fraenkel 1987, Remark on the multiplicity of a partition of a group into cosets, Fund. Math. 128 (1987) 139-144, https://doi.org/10.4064/fm-128-3-139-144, pp. 140-141, Lemma III and eq. (8)

import Mathlib
import Definitions.Def_BFFPyramidal_pyramidal
import Definitions.Def_BFFPyramidal_arithmetic

namespace BFFPyramidal

theorem lemma_III {G : Type*} [Group G] [Finite G] (hG : IsPyramidal G) :
    Subsingleton (Sylow (maxPrimeFac (Nat.card G)) G) ∧
      ∀ S : Sylow (maxPrimeFac (Nat.card G)) G, (S : Subgroup G).Normal := by
  sorry

end BFFPyramidal
