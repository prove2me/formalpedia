-- Prove2me | solution 1 for groupCohomology.coind_cocycles1_mem_coboundaries1_of_eval_one_mem_coboundaries1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/e9cbd5ec-d1ea-50b9-b7b4-9ae4f240b18a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_coind_cocycles1_mem_coboundaries1_of_eval_one_mem_coboundaries1

set_option autoImplicit false

universe u

open CategoryTheory

open groupCohomology in
theorem solution {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) (N : Rep.{u} k S)
    (c : groupCohomology.cocycles₁ (Rep.coind S.subtype N))
    (hc : (fun s : S => ((c (s : G) : Rep.coind S.subtype N) : G → N) 1) ∈ groupCohomology.coboundaries₁ N) :
    (c : G → Rep.coind S.subtype N) ∈ groupCohomology.coboundaries₁ (Rep.coind S.subtype N) := by
  classical
  obtain ⟨n, hn⟩ := hc
  have hn' : ∀ s : S, ((c (s : G) : Rep.coind S.subtype N) : G → N) 1 = N.ρ s n - n := fun s => by
    have := congrFun hn s; rw [d₀₁_hom_apply] at this; exact this.symm

  let rep : G → G := fun g => (Quotient.mk (QuotientGroup.rightRel S) g).out
  have rep_spec : ∀ g : G, g * (rep g)⁻¹ ∈ S := fun g =>
    QuotientGroup.rightRel_apply.1 (Quotient.mk_out (s := QuotientGroup.rightRel S) g)

  have I1 : ∀ g x : G, ((c g : Rep.coind S.subtype N) : G → N) x
      = ((c (x * g) : Rep.coind S.subtype N) : G → N) 1 - ((c x : Rep.coind S.subtype N) : G → N) 1 := by
    intro g x
    have h := (mem_cocycles₁_iff (c : G → Rep.coind S.subtype N)).1 c.2 x g
    have := congrArg (fun f : Rep.coind S.subtype N => (f : G → N) 1) h
    simp only [Submodule.coe_add] at this
    rw [this, Pi.add_apply]
    show _ = ((c g : Rep.coind S.subtype N) : G → N) (1 * x) + _ - _
    rw [one_mul, add_sub_cancel_right]
  have I2 : ∀ (s : S) (y : G), ((c ((s : G) * y) : Rep.coind S.subtype N) : G → N) 1
      = N.ρ s (((c y : Rep.coind S.subtype N) : G → N) 1) + ((c (s : G) : Rep.coind S.subtype N) : G → N) 1 := by
    intro s y
    have h := (mem_cocycles₁_iff (c : G → Rep.coind S.subtype N)).1 c.2 (s : G) y
    have := congrArg (fun f : Rep.coind S.subtype N => (f : G → N) 1) h
    simp only [Submodule.coe_add] at this
    rw [this, Pi.add_apply]
    congr 1
    show ((c y : Rep.coind S.subtype N) : G → N) (1 * (s : G)) = _
    rw [one_mul, ← mul_one (s : G)]
    exact (c y : Rep.coind S.subtype N).2 s 1

  let f₀fun : G → N := fun x => N.ρ ⟨x * (rep x)⁻¹, rep_spec x⟩
    (((c (rep x) : Rep.coind S.subtype N) : G → N) 1 + n)
  have rep_mul : ∀ (s : S) (g : G), rep ((s : G) * g) = rep g := fun s g => by
    show (Quotient.mk _ ((s : G) * g)).out = (Quotient.mk _ g).out
    congr 1
    apply Quotient.sound
    show @Setoid.r _ (QuotientGroup.rightRel S) ((s : G) * g) g
    rw [QuotientGroup.rightRel_apply]; simp
  have hf₀ : f₀fun ∈ Representation.coindV S.subtype N.ρ := by
    intro s x
    simp only [Subgroup.coe_subtype]
    show N.ρ ⟨(s : G) * x * (rep ((s : G) * x))⁻¹, rep_spec _⟩ _ = N.ρ s (N.ρ ⟨x * (rep x)⁻¹, rep_spec x⟩ _)
    rw [← Module.End.mul_apply, ← map_mul]
    have e : (⟨(s : G) * x * (rep ((s : G) * x))⁻¹, rep_spec _⟩ : S) = s * ⟨x * (rep x)⁻¹, rep_spec x⟩ := by
      apply Subtype.ext; simp only [Subgroup.coe_mul, rep_mul, mul_assoc]
    rw [e, rep_mul]
  refine ⟨⟨f₀fun, hf₀⟩, funext fun g => Subtype.ext (funext fun x => ?_)⟩

  rw [d₀₁_hom_apply]
  show f₀fun (x * g) - f₀fun x = ((c g : Rep.coind S.subtype N) : G → N) x
  have key : ∀ y : G, f₀fun y = ((c y : Rep.coind S.subtype N) : G → N) 1 + n := by
    intro y
    have hy : y = ((⟨y * (rep y)⁻¹, rep_spec y⟩ : S) : G) * rep y := by simp
    conv_rhs => rw [hy, I2, hn']
    show N.ρ ⟨y * (rep y)⁻¹, rep_spec y⟩ (((c (rep y) : Rep.coind S.subtype N) : G → N) 1 + n) = _
    rw [map_add]; abel
  rw [key, key, I1 g x]
  abel

end S_groupCohomology_coind_cocycles1_mem_coboundaries1_of_eval_one_mem_coboundaries1
end P2MW
export P2MW.S_groupCohomology_coind_cocycles1_mem_coboundaries1_of_eval_one_mem_coboundaries1 (solution)
