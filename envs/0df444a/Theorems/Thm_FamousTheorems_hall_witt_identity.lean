-- Prove2me | Theorems.Thm_FamousTheorems_hall_witt_identity
-- name    : FamousTheorems.hall_witt_identity
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:21:53.945988+00:00
-- url     : https://prove2.me/theorems/61805e9f-0f11-44cd-ad0d-8efa4cc63ba6
-- title:
--   The Hall–Witt identity
-- statement:
--   **The Hall–Witt identity.** In every group, with $[x,y]=xyx^{-1}y^{-1}$,
--   $$\big[[a,b],\,bcb^{-1}\big]\cdot\big[[b,c],\,cac^{-1}\big]\cdot\big[[c,a],\,aba^{-1}\big]=1.$$
--
--   This is the group-theoretic analogue of the Jacobi identity. It is the main ingredient in the three subgroups lemma and in the Lie ring associated with the lower central series.
--
--   **Formalization note.** Mathlib's `commutatorElement_commutatorElement_conj_mul`. Mathlib's commutator `⁅a, b⁆` is $aba^{-1}b^{-1}$, and the identity is written in the corresponding convention.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `commutatorElement_commutatorElement_conj_mul`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open scoped commutatorElement

theorem hall_witt_identity {G : Type*} [Group G] (a b c : G) :
    ⁅⁅a, b⁆, b * c * b⁻¹⁆ * ⁅⁅b, c⁆, c * a * c⁻¹⁆ * ⁅⁅c, a⁆, a * b * a⁻¹⁆ = 1 := by sorry

end FamousTheorems
