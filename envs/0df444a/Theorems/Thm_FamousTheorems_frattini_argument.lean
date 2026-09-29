-- Prove2me | Theorems.Thm_FamousTheorems_frattini_argument
-- name    : FamousTheorems.frattini_argument
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:05:23.402934+00:00
-- url     : https://prove2.me/theorems/a19f7342-693e-4a94-8a2d-2825b9e8acd8
-- title:
--   The Frattini argument
-- statement:
--   **The Frattini argument.** Let $N$ be a normal subgroup of a group $G$ with finitely many Sylow $p$-subgroups, and let $P$ be a Sylow $p$-subgroup of $N$. Then
--   $$G=N_G(P)\,N.$$
--
--   The reason is that $G$ acts on the Sylow $p$-subgroups of $N$ by conjugation, and $N$ already acts transitively on them. The Frattini argument is a standard tool in finite group theory. It is used to show that the Frattini subgroup of a finite group is nilpotent and in the Schur–Zassenhaus and Hall theorems.
--
--   **Formalization note.** Mathlib's `Sylow.normalizer_sup_eq_top`. `P` is a Sylow subgroup of the subgroup `N` (as a group), mapped into `G` via `N.subtype`. `Subgroup.normalizer` is its normalizer in `G`, and `⊔` is the join of subgroups, which equals the product $N_G(P)N$ because $N$ is normal. The finiteness hypothesis is `Finite (Sylow p N)`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Sylow.normalizer_sup_eq_top`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem frattini_argument {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] {N : Subgroup G} [N.Normal] [Finite (Sylow p N)]
    (P : Sylow p N) :
    Subgroup.normalizer (((P : Subgroup N).map N.subtype : Subgroup G) : Set G) ⊔ N = ⊤ := by sorry

end FamousTheorems
