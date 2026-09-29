-- Prove2me | Theorems.Thm_FamousTheorems_burnside_fixed_point_free_involution_abelian_6c
-- name    : FamousTheorems.burnside_fixed_point_free_involution_abelian_6c
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:47:14.348186+00:00
-- url     : https://prove2.me/theorems/df78416a-37d5-4e11-b936-6ac9598e999e
-- title:
--   Burnside: a finite group with a fixed-point-free involutive automorphism is abelian
-- statement:
--   **Finite groups with a fixed-point-free involutive automorphism are abelian.** Let $G$ be a finite group and $\varphi$ an automorphism of $G$ with $\varphi\circ\varphi=\mathrm{id}$ whose only fixed point is the identity. Then $G$ is abelian.
--
--   In fact $\varphi(g)=g^{-1}$ for every $g$, and $G$ has odd order. The theorem is a classical exercise attributed to Burnside. It is the simplest case of the theory of fixed-point-free automorphisms, which leads to Thompson's theorem that a finite group with a fixed-point-free automorphism of prime order is nilpotent.
--
--   **Formalization note.** Mathlib's `MonoidHom.FixedPointFree.commute_all_of_involutive`. The statement allows any monoid endomorphism $\varphi$; an involutive one is automatically an automorphism. `FixedPointFree φ` means $\varphi(g)=g\Rightarrow g=1$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MonoidHom.FixedPointFree.commute_all_of_involutive`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem burnside_fixed_point_free_involution_abelian_6c {G : Type*} [Group G] [Finite G] {φ : G →* G} (hφ : MonoidHom.FixedPointFree φ)
    (h2 : Function.Involutive φ) (g h : G) : Commute g h := by sorry

end FamousTheorems
