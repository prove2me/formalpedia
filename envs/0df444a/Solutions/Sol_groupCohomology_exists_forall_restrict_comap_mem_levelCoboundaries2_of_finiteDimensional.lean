-- Prove2me | solution 1 for groupCohomology.exists_forall_restrict_comap_mem_levelCoboundaries2_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/feea83ad-b881-5b8b-845e-8d32c7879aec

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_forall_restrict_comap_mem_levelCoboundaries2_of_finiteDimensional

set_option autoImplicit false
set_option maxHeartbeats 3200000
open groupCohomology

theorem solution
    {p : ℕ} [Fact p.Prime] {Γ : Type} [Group Γ]
    (r : Γ →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (T : ℕ → Subgroup Γ) (hT : ∀ N M : ℕ, 0 < N → N ∣ M → T M ≤ T N)
    (S : Subgroup Γ) (B : Rep.{0} (ZMod p) S) (N₀ : ℕ) (hN₀ : 0 < N₀)
    (hfin : FiniteDimensional (ZMod p)
      (continuousH2 (r.comp (S ⊓ T N₀).subtype) (Rep.res (Subgroup.inclusion (inf_le_left : S ⊓ T N₀ ≤ S)) B)))
    (hvanish : ∀ z : ↥(S ⊓ T N₀) × ↥(S ⊓ T N₀) → B,
      z ∈ levelCocycles₂ (r.comp (S ⊓ T N₀).subtype) (Rep.res (Subgroup.inclusion (inf_le_left : S ⊓ T N₀ ≤ S)) B) →
      ∃ (N : ℕ) (_ : 0 < N),
        (fun g : ↥((T N).comap (S ⊓ T N₀).subtype) × ↥((T N).comap (S ⊓ T N₀).subtype) =>
            z (((T N).comap (S ⊓ T N₀).subtype).subtype g.1, ((T N).comap (S ⊓ T N₀).subtype).subtype g.2))
          ∈ levelCoboundaries₂ ((r.comp (S ⊓ T N₀).subtype).comp ((T N).comap (S ⊓ T N₀).subtype).subtype)
              (Rep.res ((T N).comap (S ⊓ T N₀).subtype).subtype (Rep.res (Subgroup.inclusion (inf_le_left : S ⊓ T N₀ ≤ S)) B))) :
    ∃ (N : ℕ) (hle : (T N).comap S.subtype ≤ (T N₀).comap S.subtype), 0 < N ∧ N₀ ∣ N ∧
      ∀ b : ↥((T N₀).comap S.subtype) × ↥((T N₀).comap S.subtype) → B,
        b ∈ levelCocycles₂ ((r.comp S.subtype).comp ((T N₀).comap S.subtype).subtype) (Rep.res ((T N₀).comap S.subtype).subtype B) →
        (fun g : ↥((T N).comap S.subtype) × ↥((T N).comap S.subtype) => b (Subgroup.inclusion hle g.1, Subgroup.inclusion hle g.2))
          ∈ levelCoboundaries₂ ((r.comp S.subtype).comp ((T N).comap S.subtype).subtype) (Rep.res ((T N).comap S.subtype).subtype B) := by
  classical

  let U : ℕ → Subgroup S := fun M => (T M).comap S.subtype
  let S' : Subgroup Γ := S ⊓ T N₀
  let U' : ℕ → Subgroup S' := fun M => (T M).comap S'.subtype
  let ι : ↥S' →* ↥S := Subgroup.inclusion (inf_le_left : S ⊓ T N₀ ≤ S)
  let B' : Rep.{0} (ZMod p) ↥S' := Rep.res ι B
  haveI := hfin

  let toU : ↥S' →* ↥(U N₀) :=
    { toFun := fun g => ⟨⟨g.1, g.2.1⟩, g.2.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl }

  let bs := Module.finBasis (ZMod p) (continuousH2 (r.comp S'.subtype) B')
  have hrep : ∀ i, ∃ z : levelCocycles₂ (r.comp S'.subtype) B', continuousH2π _ B' z = bs i :=
    fun i => Submodule.mkQ_surjective _ (bs i)
  choose z hz using hrep

  have hdie := fun i => hvanish (z i) (z i).2
  choose Ni hNi hzi using hdie

  let N : ℕ := N₀ * ∏ i, Ni i
  have hN : 0 < N := Nat.mul_pos hN₀ (Finset.prod_pos fun i _ => hNi i)
  have hN₀N : N₀ ∣ N := dvd_mul_right _ _
  have hNiN : ∀ i, Ni i ∣ N := fun i => (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)).mul_left N₀
  have hle : U N ≤ U N₀ := Subgroup.comap_mono (hT N₀ N hN₀ hN₀N)
  have hj : ∀ i, U' N ≤ U' (Ni i) := fun i => Subgroup.comap_mono (hT (Ni i) N (hNi i) (hNiN i))

  let RN : (↥S' × ↥S' → B') →ₗ[ZMod p] (↥(U' N) × ↥(U' N) → Rep.res (U' N).subtype B') :=
    cochainsPullPush₂ (A := B') (B := Rep.res (U' N).subtype B') (U' N).subtype LinearMap.id
  have hRNcob : ∀ x : ↥S' × ↥S' → B', x ∈ levelCoboundaries₂ (r.comp S'.subtype) B' →
      RN x ∈ levelCoboundaries₂ ((r.comp S'.subtype).comp (U' N).subtype) (Rep.res (U' N).subtype B') := fun x hx =>
    cochainsPullPush₂_mem_levelCoboundaries₂ (rH := r.comp S'.subtype) (rG := (r.comp S'.subtype).comp (U' N).subtype)
      (A := B') (B := Rep.res (U' N).subtype B') (U' N).subtype (fun _ => rfl) LinearMap.id (fun _ _ => rfl) hx
  have hzN : ∀ i, RN (z i : ↥S' × ↥S' → B') ∈ levelCoboundaries₂ ((r.comp S'.subtype).comp (U' N).subtype) (Rep.res (U' N).subtype B') := by
    intro i
    have h := cochainsPullPush₂_mem_levelCoboundaries₂ (rH := (r.comp S'.subtype).comp (U' (Ni i)).subtype)
      (rG := (r.comp S'.subtype).comp (U' N).subtype) (A := Rep.res (U' (Ni i)).subtype B') (B := Rep.res (U' N).subtype B')
      (Subgroup.inclusion (hj i)) (fun _ => rfl) LinearMap.id (fun _ _ => rfl) (hzi i)
    have heq : (cochainsPullPush₂ (A := Rep.res (U' (Ni i)).subtype B') (B := Rep.res (U' N).subtype B')
          (Subgroup.inclusion (hj i)) LinearMap.id
          (fun g : ↥(U' (Ni i)) × ↥(U' (Ni i)) => (z i : ↥S' × ↥S' → B') ((U' (Ni i)).subtype g.1, (U' (Ni i)).subtype g.2)))
        = RN (z i : ↥S' × ↥S' → B') := by
      funext g
      rfl
    rw [heq] at h
    exact h
  refine ⟨N, hle, hN, hN₀N, fun b hb => ?_⟩

  let b' : ↥S' × ↥S' → B' := fun g => b (toU g.1, toU g.2)
  have hb' : b' ∈ levelCocycles₂ (r.comp S'.subtype) B' :=
    cochainsPullPush₂_mem_levelCocycles₂ (rH := (r.comp S.subtype).comp (U N₀).subtype) (rG := r.comp S'.subtype)
      (A := Rep.res (U N₀).subtype B) (B := B') toU (fun _ => rfl) LinearMap.id (fun _ _ => rfl) hb

  let x : levelCocycles₂ (r.comp S'.subtype) B' := ⟨b', hb'⟩
  let c := bs.repr (continuousH2π _ B' x)
  let w : levelCocycles₂ (r.comp S'.subtype) B' := ∑ i, c i • z i
  have hxw : ((x - w : levelCocycles₂ (r.comp S'.subtype) B') : ↥S' × ↥S' → B') ∈ levelCoboundaries₂ (r.comp S'.subtype) B' := by
    rw [← continuousH2π_eq_zero_iff, map_sub, sub_eq_zero]
    show continuousH2π _ B' x = continuousH2π _ B' (∑ i, c i • z i)
    rw [map_sum]
    simp_rw [map_smul, hz]
    exact (bs.sum_repr _).symm

  have hRNw : RN (w : ↥S' × ↥S' → B') ∈ levelCoboundaries₂ ((r.comp S'.subtype).comp (U' N).subtype) (Rep.res (U' N).subtype B') := by
    have : (w : ↥S' × ↥S' → B') = ∑ i, c i • (z i : ↥S' × ↥S' → B') := by
      show ((∑ i, c i • z i : levelCocycles₂ (r.comp S'.subtype) B') : ↥S' × ↥S' → B') = _
      rw [Submodule.coe_sum]
      rfl
    rw [this, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (hzN i)
  have hRNb : RN b' ∈ levelCoboundaries₂ ((r.comp S'.subtype).comp (U' N).subtype) (Rep.res (U' N).subtype B') := by
    have hsplit : b' = ((x - w : levelCocycles₂ (r.comp S'.subtype) B') : ↥S' × ↥S' → B') + (w : ↥S' × ↥S' → B') := by
      rw [Submodule.coe_sub, sub_add_cancel]
    rw [hsplit, map_add]
    exact Submodule.add_mem _ (hRNcob _ hxw) hRNw

  let θ : ↥(U N) →* ↥(U' N) :=
    { toFun := fun v => ⟨⟨(v.1 : Γ), ⟨v.1.2, hle v.2⟩⟩, v.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have key := cochainsPullPush₂_mem_levelCoboundaries₂ (rH := (r.comp S'.subtype).comp (U' N).subtype)
    (rG := (r.comp S.subtype).comp (U N).subtype) (A := Rep.res (U' N).subtype B') (B := Rep.res (U N).subtype B)
    θ (fun _ => rfl) LinearMap.id (fun _ _ => rfl) hRNb
  have hfun : (fun g : ↥(U N) × ↥(U N) => b (Subgroup.inclusion hle g.1, Subgroup.inclusion hle g.2))
      = cochainsPullPush₂ (A := Rep.res (U' N).subtype B') (B := Rep.res (U N).subtype B) θ LinearMap.id (RN b') :=
    funext fun _ => rfl
  show (fun g : ↥(U N) × ↥(U N) => b (Subgroup.inclusion hle g.1, Subgroup.inclusion hle g.2)) ∈ _
  rw [hfun]
  exact key

end S_groupCohomology_exists_forall_restrict_comap_mem_levelCoboundaries2_of_finiteDimensional
end P2MW
export P2MW.S_groupCohomology_exists_forall_restrict_comap_mem_levelCoboundaries2_of_finiteDimensional (solution)
