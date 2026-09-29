-- Prove2me | solution 1 for groupCohomology.inflationImage_eq_inflationImage_of_forall_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/c320b728-6b5d-5d3c-b3f9-027501810a26

import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import Theorems.Thm_groupCohomology_mem_inflationImage_iff_exists_cocycles1_apply_eq_zero
import Theorems.Thm_groupCohomology_inflationImage_antitone
import Theorems.Thm_groupCohomology_subsingleton_H1_of_isUnit_card
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_inflationImage_eq_inflationImage_of_forall_pow_mem

set_option autoImplicit false
open CategoryTheory Module groupCohomology

universe u

theorem solution
    {k G : Type u} [Field k] [Group G] (M : Rep k G)
    (U W : Subgroup G) [U.Normal] [W.Normal] [U.FiniteIndex] (hUW : U ≤ W)
    (q : ℕ) [Fact q.Prime] (hq : (q : k) ≠ 0)
    (hW : ∀ w ∈ W, ∃ a : ℕ, w ^ (q ^ a) ∈ U) :
    inflationImage M U = inflationImage M W := by
  classical
  refine le_antisymm ?_ (inflationImage_antitone M hUW)
  intro x hx
  obtain ⟨c, rfl, hcU⟩ := (mem_inflationImage_iff_exists_cocycles1_apply_eq_zero M U x).1 hx

  let U' : Subgroup W := U.subgroupOf W
  haveI : U'.Normal := inferInstance
  haveI : U'.FiniteIndex := inferInstance
  haveI : Fintype (W ⧸ U') := Fintype.ofFinite _

  have hP : IsPGroup q (W ⧸ U') := by
    intro y
    induction y using QuotientGroup.induction_on with | H w =>
    obtain ⟨a, ha⟩ := hW w.1 w.2
    refine ⟨a, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    change ((w ^ q ^ a : W) : G) ∈ U
    rw [Subgroup.coe_pow]
    exact ha
  have hunit : IsUnit ((Fintype.card (W ⧸ U') : k)) := by
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [← Nat.card_eq_fintype_card, hn, Nat.cast_pow]
    exact isUnit_iff_ne_zero.2 (pow_ne_zero _ hq)

  let MW := Rep.res W.subtype M
  let cW : cocycles₁ MW := mapCocycles₁ W.subtype (𝟙 MW) c
  have hcW : ∀ w : W, cW w = c (w : G) := fun w => rfl
  have h1 : H1π MW cW ∈ inflationImage MW U' :=
    (mem_inflationImage_iff_exists_cocycles1_apply_eq_zero MW U' _).2
      ⟨cW, rfl, fun u hu => by rw [hcW]; exact hcU u.1 hu⟩
  haveI hss : Subsingleton (H1 (MW.quotientToInvariants U')) :=
    subsingleton_H1_of_isUnit_card _ hunit
  have h0 : H1π MW cW = 0 := by
    obtain ⟨y, hy⟩ := h1
    rw [← hy, Subsingleton.elim y 0, map_zero]
  obtain ⟨m₀, hm₀⟩ := (H1π_eq_zero_iff cW).1 h0
  have hcw : ∀ w ∈ W, c w = M.ρ w m₀ - m₀ := by
    intro w hw
    have := congr_fun hm₀ ⟨w, hw⟩
    rw [d₀₁_hom_apply] at this
    exact this.symm

  let d : cocycles₁ M := ⟨(d₀₁ M).hom m₀, d₀₁_apply_mem_cocycles₁ m₀⟩
  refine (mem_inflationImage_iff_exists_cocycles1_apply_eq_zero M W _).2 ⟨c - d, ?_, fun w hw => ?_⟩
  · rw [H1π_eq_iff]
    refine ⟨-m₀, funext fun g => ?_⟩
    change M.ρ g (-m₀) - (-m₀) = c g - (M.ρ g m₀ - m₀) - c g
    rw [map_neg]; abel
  · change c w - (M.ρ w m₀ - m₀) = 0
    rw [hcw w hw, sub_self]

end S_groupCohomology_inflationImage_eq_inflationImage_of_forall_pow_mem
end P2MW
export P2MW.S_groupCohomology_inflationImage_eq_inflationImage_of_forall_pow_mem (solution)
