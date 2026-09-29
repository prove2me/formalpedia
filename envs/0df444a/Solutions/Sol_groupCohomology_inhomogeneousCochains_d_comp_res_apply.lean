-- Prove2me | solution 1 for groupCohomology.inhomogeneousCochains_d_comp_res_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/2a603433-3e19-597d-b503-56e8404508fa

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_inhomogeneousCochains_d_comp_res_apply

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem PlumbD.neg_one_pow_smul_eq_zsmul {k M : Type} [Ring k] [AddCommGroup M] [Module k M] (m : ℕ) (a : M) :
    (-1 : k) ^ m • a = ((-1 : ℤ) ^ m) • a := by
  rw [← Int.cast_smul_eq_zsmul k, Int.cast_pow, Int.cast_neg, Int.cast_one]

theorem solution
    {k G H : Type} [CommRing k] [Group G] [Group H] {A : Rep.{0} k G} {B : Rep.{0} k H}
    (f : H →* G) (T : A →+ B) (hT : ∀ (h : H) (a : A), T (A.ρ (f h) a) = B.ρ h (T a)) (n : ℕ)
    (x : (Fin n → G) → A) :
    ((inhomogeneousCochains B).d n (n + 1)).hom (fun g => T (x (f ∘ g))) =
      fun g => T (((inhomogeneousCochains A).d n (n + 1)).hom x (f ∘ g)) := by
  ext g
  rw [inhomogeneousCochains.d_def, inhomogeneousCochains.d_def, inhomogeneousCochains.d_hom_apply,
    inhomogeneousCochains.d_hom_apply, map_add, map_sum]
  have h0 : T ((A.ρ ((⇑f ∘ g) 0)) (x fun i => (⇑f ∘ g) i.succ)) =
      B.ρ (g 0) (T (x (⇑f ∘ fun i => g i.succ))) := hT (g 0) _
  rw [h0]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [PlumbD.neg_one_pow_smul_eq_zsmul (k := k) (M := B), PlumbD.neg_one_pow_smul_eq_zsmul (k := k) (M := A),
    map_zsmul, Fin.comp_contractNth (· * ·) (· * ·) (fun a b => map_mul f a b)]

end S_groupCohomology_inhomogeneousCochains_d_comp_res_apply
end P2MW
export P2MW.S_groupCohomology_inhomogeneousCochains_d_comp_res_apply (solution)
