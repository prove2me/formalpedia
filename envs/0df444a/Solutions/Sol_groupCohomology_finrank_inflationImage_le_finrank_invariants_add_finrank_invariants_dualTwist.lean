-- Prove2me | solution 1 for groupCohomology.finrank_inflationImage_le_finrank_invariants_add_finrank_invariants_dualTwist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/db121d21-edbe-5e20-8a86-f3dcb50cc283

import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import Definitions.Def_GroupCohomology_Selmer
import Definitions.Def_GroupCohomology_TateTwist
import Theorems.Thm_groupCohomology_inflationImage_eq_inflationImage_of_forall_pow_mem
import Theorems.Thm_groupCohomology_finrank_invariants_dualTwist_eq_finrank_ker_coinvariants_sub_smul
import Theorems.Thm_groupCohomology_finrank_ker_frobeniusOnCoinvariants_le_finrank_ker_of_model
import Theorems.Thm_groupCohomology_finrank_inflationImage_eq_finrank_H1_quotientToInvariants
import Theorems.Thm_groupCohomology_finrank_H1_le_finrank_invariants_add_finrank_ker_of_cyclic_quotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finrank_inflationImage_le_finrank_invariants_add_finrank_invariants_dualTwist

set_option autoImplicit false
open CategoryTheory Module groupCohomology

universe u

theorem solution
    {k G : Type u} [Field k] [Group G] (M : Rep k G) [FiniteDimensional k M]
    (χ : G →* kˣ)
    (U W I : Subgroup G) [U.Normal] [W.Normal] [I.Normal] [U.FiniteIndex] [W.FiniteIndex]
    (hU : ∀ u ∈ U, M.ρ u = 1) (hUW : U ≤ W)
    (q : ℕ) [Fact q.Prime] (hq : (q : k) ≠ 0) (hW : ∀ w ∈ W, ∃ a : ℕ, w ^ (q ^ a) ∈ U)
    (t : G) (ht : t ∈ I) (htame : ∀ i ∈ I, ∃ a : ℕ, (t ^ a)⁻¹ * i ∈ W)
    (φ : G) (hgen : ∀ g, ∃ n : ℕ, (φ ^ n)⁻¹ * g ∈ I ⊔ U)
    (hχI : ∀ i ∈ I, χ i = 1) (hχU : ∀ u ∈ U, χ u = 1) (hχφ : (χ φ : k) = q)
    (m : ℕ) (hmq : (m : k) * q = 1)
    (hm : (QuotientGroup.mk φ : G ⧸ W)⁻¹ * QuotientGroup.mk t * QuotientGroup.mk φ
      = (QuotientGroup.mk t : G ⧸ W) ^ m)
    (hst : (QuotientGroup.mk φ : G ⧸ W) * QuotientGroup.mk t * (QuotientGroup.mk φ)⁻¹
      ∈ Subgroup.zpowers (QuotientGroup.mk t : G ⧸ W)) :
    finrank k (inflationImage M U)
      ≤ finrank k M.ρ.invariants + finrank k (M.dualTwist χ).ρ.invariants := by
  classical

  rw [inflationImage_eq_inflationImage_of_forall_pow_mem M U W hUW q hq hW,
    finrank_inflationImage_eq_finrank_H1_quotientToInvariants M W]
  set A := M.quotientToInvariants W with hA
  haveI : FiniteDimensional k A :=
    inferInstanceAs (FiniteDimensional k (Representation.invariants (M.ρ.comp W.subtype)))
  haveI : Fintype (G ⧸ W) := Fintype.ofFinite _

  let S : Subgroup (G ⧸ W) := I.map (QuotientGroup.mk' W)
  haveI hSN : S.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective W)
  haveI : Fintype ((G ⧸ W) ⧸ S) := Fintype.ofFinite _
  have htS : (QuotientGroup.mk t : G ⧸ W) ∈ S := ⟨t, ht, rfl⟩
  have hSt : S ≤ Subgroup.zpowers (QuotientGroup.mk t : G ⧸ W) := by
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨a, ha⟩ := htame i hi
    refine ⟨a, ?_⟩
    change (QuotientGroup.mk t : G ⧸ W) ^ (a : ℤ) = QuotientGroup.mk i
    rw [zpow_natCast, ← QuotientGroup.mk_pow, QuotientGroup.eq]
    exact ha
  have hIU_S : ∀ g ∈ I ⊔ U, (QuotientGroup.mk g : G ⧸ W) ∈ S := by
    have hle : (I ⊔ U).map (QuotientGroup.mk' W) ≤ S := by
      rw [Subgroup.map_sup]
      refine sup_le le_rfl ?_
      rintro _ ⟨u, hu, rfl⟩
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff u).2 (hUW hu)]
      exact S.one_mem
    intro g hg
    exact hle ⟨g, hg, rfl⟩
  have hφgen : ∀ x : (G ⧸ W) ⧸ S,
      x ∈ Subgroup.zpowers (QuotientGroup.mk (QuotientGroup.mk φ : G ⧸ W) : (G ⧸ W) ⧸ S) := by
    intro x
    induction x using QuotientGroup.induction_on with | H y =>
    induction y using QuotientGroup.induction_on with | H g =>
    obtain ⟨n, hn⟩ := hgen g
    refine ⟨n, ?_⟩
    change (QuotientGroup.mk (QuotientGroup.mk φ : G ⧸ W) : (G ⧸ W) ⧸ S) ^ (n : ℤ)
      = QuotientGroup.mk (QuotientGroup.mk g)
    rw [zpow_natCast, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow, QuotientGroup.eq,
      ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    exact hIU_S _ hn

  have h3 := finrank_H1_le_finrank_invariants_add_finrank_ker_of_cyclic_quotient A S
    (QuotientGroup.mk t) htS hSt hφgen m hm hst

  let eqv : A.ρ.invariants ≃ₗ[k] M.ρ.invariants :=
    { toFun := fun x => ⟨x.1.1, fun g => congrArg Subtype.val (x.2 (QuotientGroup.mk g))⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun y => ⟨⟨y.1, fun s => y.2 s.1⟩, fun z => QuotientGroup.induction_on z
        fun g => Subtype.ext (y.2 g)⟩
      left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
      right_inv := fun _ => rfl }
  have h4 : finrank k A.ρ.invariants = finrank k M.ρ.invariants := eqv.finrank_eq

  let N : Subgroup G := I ⊔ U
  haveI : N.Normal := inferInstance
  let J : Submodule k M := ⨆ n ∈ N, LinearMap.range (M.ρ n - 1)
  have hJg : ∀ g : G, J ≤ J.comap (M.ρ g) := by
    intro g
    refine iSup₂_le fun n hn => ?_
    rintro _ ⟨y, rfl⟩
    rw [Submodule.mem_comap]
    have hconj : g * n * g⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance n hn g
    have : M.ρ g ((M.ρ n - 1) y) = (M.ρ (g * n * g⁻¹) - 1) (M.ρ g y) := by
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, map_mul, Module.End.mul_apply]
      rw [← Module.End.mul_apply (M.ρ g⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [this]
    exact Submodule.mem_iSup_of_mem (g * n * g⁻¹) (Submodule.mem_iSup_of_mem hconj ⟨_, rfl⟩)
  let φD : (M ⧸ J) →ₗ[k] (M ⧸ J) := J.mapQ J (M.ρ φ) (hJg φ)
  have hφD : φD ∘ₗ J.mkQ = J.mkQ ∘ₗ M.ρ φ := Submodule.mapQ_mkQ _ _ _
  have hχN : ∀ n ∈ N, χ n = 1 := by
    have hle : N ≤ MonoidHom.ker χ :=
      sup_le (fun g hg => (MonoidHom.mem_ker).2 (hχI g hg)) (fun g hg => (MonoidHom.mem_ker).2 (hχU g hg))
    exact fun n hn => (MonoidHom.mem_ker).1 (hle hn)
  have h5 := finrank_invariants_dualTwist_eq_finrank_ker_coinvariants_sub_smul M χ N hχN φ hgen
    (q : k) hχφ (M ⧸ J) J.mkQ (Submodule.mkQ_surjective J) (Submodule.ker_mkQ J) φD hφD

  let augW : Submodule k M := ⨆ w ∈ W, LinearMap.range (M.ρ w - 1)
  let J₂ : Submodule k M := augW ⊔ LinearMap.range (M.ρ t - 1)
  have haugW : ∀ g : G, augW ≤ augW.comap (M.ρ g) := by
    intro g
    refine iSup₂_le fun w hw => ?_
    rintro _ ⟨y, rfl⟩
    rw [Submodule.mem_comap]
    have hconj : g * w * g⁻¹ ∈ W := Subgroup.Normal.conj_mem inferInstance w hw g
    have : M.ρ g ((M.ρ w - 1) y) = (M.ρ (g * w * g⁻¹) - 1) (M.ρ g y) := by
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, map_mul, Module.End.mul_apply]
      rw [← Module.End.mul_apply (M.ρ g⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [this]
    exact Submodule.mem_iSup_of_mem (g * w * g⁻¹) (Submodule.mem_iSup_of_mem hconj ⟨_, rfl⟩)

  have hpow : ∀ (a : ℕ) (z : M), M.ρ (t ^ a) z - z ∈ LinearMap.range (M.ρ t - 1) := by
    intro a z
    induction a with
    | zero => rw [pow_zero, map_one, Module.End.one_apply, sub_self]; exact Submodule.zero_mem _
    | succ a ih =>
      have : M.ρ (t ^ (a + 1)) z - z = (M.ρ t - 1) (M.ρ (t ^ a) z) + (M.ρ (t ^ a) z - z) := by
        rw [pow_succ', map_mul, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply]
        abel
      rw [this]
      exact (LinearMap.range (M.ρ t - 1)).add_mem ⟨_, rfl⟩ ih

  have hmem_tw : ∀ (a : ℕ) (w : G), w ∈ W → ∀ z, M.ρ (t ^ a * w) z - z ∈ J₂ := by
    intro a w hw z
    have : M.ρ (t ^ a * w) z - z = M.ρ (t ^ a) ((M.ρ w - 1) z) + (M.ρ (t ^ a) z - z) := by
      rw [map_mul, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub]
      abel
    rw [this]
    refine J₂.add_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right (hpow a z))
    exact haugW (t ^ a) (Submodule.mem_iSup_of_mem w (Submodule.mem_iSup_of_mem hw ⟨z, rfl⟩))
  have hJ₂g : ∀ g : G, J₂ ≤ J₂.comap (M.ρ g) := by
    intro g
    refine sup_le ((haugW g).trans (Submodule.comap_mono le_sup_left)) ?_
    rintro _ ⟨z, rfl⟩
    rw [Submodule.mem_comap]
    have hconj : g * t * g⁻¹ ∈ I := Subgroup.Normal.conj_mem inferInstance t ht g
    obtain ⟨a, ha⟩ := htame _ hconj
    have heq : g * t * g⁻¹ = t ^ a * ((t ^ a)⁻¹ * (g * t * g⁻¹)) := by group
    have : M.ρ g ((M.ρ t - 1) z) = M.ρ (g * t * g⁻¹) (M.ρ g z) - M.ρ g z := by
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, map_mul, Module.End.mul_apply]
      rw [← Module.End.mul_apply (M.ρ g⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [this, heq]
    exact hmem_tw a _ ha _

  let Sg : Subgroup G :=
    { carrier := {g | ∀ z, M.ρ g z - z ∈ J₂}
      mul_mem' := fun {x y} hx hy z => by
        have : M.ρ (x * y) z - z = M.ρ x (M.ρ y z - z) + (M.ρ x z - z) := by
          rw [map_mul, Module.End.mul_apply, map_sub]; abel
        rw [this]
        exact J₂.add_mem (hJ₂g x (hy z)) (hx z)
      one_mem' := fun z => by
        rw [map_one, Module.End.one_apply, sub_self]; exact J₂.zero_mem
      inv_mem' := fun {x} hx z => by
        have : M.ρ x⁻¹ z - z = -(M.ρ x⁻¹ (M.ρ x z - z)) := by
          rw [map_sub, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
            Module.End.one_apply, neg_sub]
        rw [this]
        exact J₂.neg_mem (hJ₂g x⁻¹ (hx z)) }
  have hNSg : N ≤ Sg := by
    refine sup_le ?_ ?_
    · intro i hi z
      obtain ⟨a, ha⟩ := htame i hi
      have heq : i = t ^ a * ((t ^ a)⁻¹ * i) := by group
      rw [heq]
      exact hmem_tw a _ ha z
    · intro u hu z
      change M.ρ u z - z ∈ J₂
      rw [hU u hu, Module.End.one_apply, sub_self]
      exact J₂.zero_mem
  have hJ₂ : J ≤ J₂ := by
    refine iSup₂_le fun n hn => ?_
    rintro _ ⟨z, rfl⟩
    exact hNSg hn z
  have hkerJ : LinearMap.ker J.mkQ ≤ augW ⊔ LinearMap.range (M.ρ t - 1) := by
    rw [Submodule.ker_mkQ]; exact hJ₂
  have hπt : LinearMap.range (M.ρ t - 1) ≤ LinearMap.ker J.mkQ := by
    rw [Submodule.ker_mkQ]
    rintro _ ⟨z, rfl⟩
    exact Submodule.mem_iSup_of_mem t (Submodule.mem_iSup_of_mem (Subgroup.mem_sup_left ht) ⟨z, rfl⟩)
  have h6 := finrank_ker_frobeniusOnCoinvariants_le_finrank_ker_of_model M U W hU q hq hW t φ hst
    (M ⧸ J) J.mkQ hkerJ hπt φD hφD m (q : k) hmq
  have h6' : finrank k (LinearMap.ker (m • frobeniusOnCoinvariants A
      (QuotientGroup.mk t) (QuotientGroup.mk φ) hst - 1)) ≤ finrank k (LinearMap.ker (φD - (q : k) • 1)) := h6
  omega

end S_groupCohomology_finrank_inflationImage_le_finrank_invariants_add_finrank_invariants_dualTwist
end P2MW
export P2MW.S_groupCohomology_finrank_inflationImage_le_finrank_invariants_add_finrank_invariants_dualTwist (solution)
