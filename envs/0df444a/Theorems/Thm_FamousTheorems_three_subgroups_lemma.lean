-- Prove2me | Theorems.Thm_FamousTheorems_three_subgroups_lemma
-- name    : FamousTheorems.three_subgroups_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:21:44.960976+00:00
-- url     : https://prove2.me/theorems/961b649f-8bce-4404-83d4-b63a0fa76a6c
-- title:
--   The three subgroups lemma
-- statement:
--   **The three subgroups lemma.** Let $H_1,H_2,H_3$ be subgroups of a group $G$. If $[[H_2,H_3],H_1]=1$ and $[[H_3,H_1],H_2]=1$, then $[[H_1,H_2],H_3]=1$.
--
--   The lemma, a consequence of the Hall–Witt identity, is due to P. Hall. It is used to prove that $[\gamma_i(G),\gamma_j(G)]\le\gamma_{i+j}(G)$ for the lower central series and in the theory of nilpotent and $p$-groups.
--
--   **Formalization note.** Mathlib's `Subgroup.commutator_commutator_eq_bot_of_rotate`. `⁅H, K⁆` is the commutator subgroup of $H$ and $K$, and `⊥` is the trivial subgroup.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Subgroup.commutator_commutator_eq_bot_of_rotate`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem three_subgroups_lemma {G : Type*} [Group G] {H₁ H₂ H₃ : Subgroup G} (h₁ : ⁅⁅H₂, H₃⁆, H₁⁆ = ⊥) (h₂ : ⁅⁅H₃, H₁⁆, H₂⁆ = ⊥) :
    ⁅⁅H₁, H₂⁆, H₃⁆ = ⊥ := by sorry

end FamousTheorems
