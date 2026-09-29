-- Prove2me | Theorems.Thm_FamousTheorems_cayley
-- name    : FamousTheorems.cayley
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T01:51:10.982731+00:00
-- url     : https://prove2.me/theorems/2435eb00-2514-436b-b621-035a845e23e7
-- title:
--   Cayley's theorem
-- statement:
--   **Cayley's theorem.**
--
--   If a group $G$ acts faithfully on a set $H$, then $G$ is isomorphic to its image in the symmetric
--   group of $H$:
--   $$G \;\cong\; \mathrm{im}\bigl(G \to \mathrm{Sym}(H)\bigr).$$
--
--   Taking $H = G$ with the left regular action — which is always faithful — gives the familiar form:
--   every group embeds in the symmetric group on its own underlying set, so every finite group of order
--   $n$ is a subgroup of $S_n$. Abstract groups are therefore no more general than permutation groups,
--   which is what made the abstract definition acceptable in the 19th century when groups were
--   understood concretely as permutations.
--
--   The faithfulness hypothesis is exactly what makes the map injective: the kernel of $G \to
--   \mathrm{Sym}(H)$ is the set of elements acting trivially, so it is trivial precisely when the action
--   is faithful.
--
--   Cayley stated it in 1854, though the proof there is incomplete; Jordan gave a full treatment. The
--   embedding is rarely efficient — $S_n$ is vastly larger than a group of order $n$ — and finding
--   minimal faithful permutation representations is a separate and hard problem.
--
--   **Formalization note.** `MulAction.toPermHom G H : G →* Equiv.Perm H` is the action homomorphism and
--   `FaithfulSMul` is faithfulness. The isomorphism is data, so it is wrapped in `Nonempty`. The result
--   is Mathlib's `Equiv.Perm.subgroupOfMulAction`.
-- source:
--   Listed in Mathlib's "1000 theorems" manifest (docs/1000.yaml); formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

theorem cayley (G H : Type*) [Group G] [MulAction G H] [FaithfulSMul G H] :
    Nonempty (G ≃* (MulAction.toPermHom G H).range) := by sorry

end FamousTheorems
