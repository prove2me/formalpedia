-- Prove2me | Theorems.Thm_BFFPyramidal_herzog_schonheim_pyramidal
-- name    : BFFPyramidal.herzog_schonheim_pyramidal
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-13T18:29:39.695472+00:00
-- url     : https://prove2.me/theorems/d7cd8e51-3e39-4a7e-b4f3-0b3b27aba5f2
-- title:
--   Herzog-Schönheim conjecture for pyramidal groups
-- statement:
--   **Herzog-Schönheim for pyramidal groups.** Let $G$ be a pyramidal group and suppose the cosets $a_iK_i$, $1 \le i \le t$, partition $G$ with $t > 1$. Then two of the indices coincide:
--   $$ \exists\, i \ne j, \qquad [G : K_i] = [G : K_j]. $$
--
--   Herzog and Schönheim conjectured this for arbitrary groups; it remains open in general, and is open even for finite solvable groups. It is a consequence of the multiplicity bound of Berger-Felzenbaum-Fraenkel, since that bound is always at least $2$.
--
--   **Formalization note.** The conclusion is stated for the indices `(K i).index`, matching the conjecture as usually stated; for a finite group equality of indices is equivalent to equality of orders. The indices $i, j$ range over the index type `Fin t`, and $i \ne j$ refers to distinct *indices*, so the two cosets are distinct parts of the partition even if the subgroups happen to be equal.
-- source:
--   Berger--Felzenbaum--Fraenkel 1987, Remark on the multiplicity of a partition of a group into cosets, Fund. Math. 128 (1987) 139-144, https://doi.org/10.4064/fm-128-3-139-144, p. 140 (statement of the conjecture) and p. 139 (the Theorem, which implies it for pyramidal groups); original problem: Herzog-Schönheim, Research problem No. 9, Canad. Math. Bull. 17 (1974) 150

import Mathlib
import Definitions.Def_BFFPyramidal_pyramidal
import Definitions.Def_BFFPyramidal_cosetPartition

namespace BFFPyramidal

theorem herzog_schonheim_pyramidal {G : Type*} [Group G] [Finite G] (hG : IsPyramidal G)
    {t : ℕ} (ht : 1 < t) (K : Fin t → Subgroup G) (a : Fin t → G)
    (hpart : IsCosetPartition K a) :
    ∃ i j : Fin t, i ≠ j ∧ (K i).index = (K j).index := by
  sorry

end BFFPyramidal
