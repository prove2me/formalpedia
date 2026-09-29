-- Prove2me | solution 1 for groupCohomology.exists_isGradedCupProduct
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/ca400652-a874-5234-bf54-f4a1ad9d91e3

import Mathlib
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Theorems.Thm_groupCohomology_d_cochainCup_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_isGradedCupProduct

set_option autoImplicit false
universe u
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory groupCohomology"

namespace P2mS26CupE

variable {k G : Type u} [CommRing k] [Group G]

theorem d_iCocycles (A : Rep.{u} k G) (n : ℕ) (x : cocycles A n) :
    (inhomogeneousCochains.d A n).hom ((iCocycles A n).hom x) = 0 := by
  have := congrArg (fun φ => φ.hom x) ((inhomogeneousCochains A).iCycles_d n (n + 1))
  simpa [ModuleCat.hom_comp] using this

theorem d_cup_eq_zero (A B : Rep.{u} k G) (p q : ℕ) (x : cocycles A p) (y : cocycles B q) :
    (inhomogeneousCochains.d (A ⊗ B) (p + q)).hom
      (cochainCup A B p q ((iCocycles A p).hom x) ((iCocycles B q).hom y)) = 0 := by
  funext σ
  rw [groupCohomology.d_cochainCup_apply, d_iCocycles, d_iCocycles, map_zero, map_zero, LinearMap.zero_apply,
    Pi.zero_apply, Pi.zero_apply, smul_zero, add_zero]

theorem π_surjective (A : Rep.{u} k G) (n : ℕ) : Function.Surjective (groupCohomology.π A n).hom :=
  (ModuleCat.epi_iff_surjective ((inhomogeneousCochains A).homologyπ n)).1 inferInstance

theorem iCocycles_injective (A : Rep.{u} k G) (n : ℕ) : Function.Injective (iCocycles A n).hom :=
  (ModuleCat.mono_iff_injective (iCocycles A n)).1 inferInstance

theorem d_cast (A : Rep.{u} k G) (n m : ℕ) (h : n + 1 = m) (u : (Fin n → G) → A) :
    ((inhomogeneousCochains A).d n m).hom u
      = fun σ => (inhomogeneousCochains.d A n).hom u (fun j => σ (Fin.cast h j)) := by
  subst h
  funext σ
  simp

theorem i_toCocycles (A : Rep.{u} k G) (i n : ℕ) (w : (inhomogeneousCochains A).X i) :
    (iCocycles A n).hom ((toCocycles A i n).hom w) = ((inhomogeneousCochains A).d i n).hom w := by
  have := congrArg (fun φ => φ.hom w) ((inhomogeneousCochains A).toCycles_i i n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  exact this

theorem π_toCocycles (A : Rep.{u} k G) (i n : ℕ) (w : (inhomogeneousCochains A).X i) :
    (groupCohomology.π A n).hom ((toCocycles A i n).hom w) = 0 := by
  have := congrArg (fun φ => φ.hom w) ((inhomogeneousCochains A).toCycles_comp_homologyπ i n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at this
  exact this

theorem toCocycles_of_not_rel (A : Rep.{u} k G) (i n : ℕ) (hi : ¬ i + 1 = n) : toCocycles A i n = 0 := by
  rw [← cancel_mono (iCocycles A n)]
  simp only [HomologicalComplex.toCycles_i, Limits.zero_comp]
  exact (inhomogeneousCochains A).shape _ _ hi

variable (A B : Rep.{u} k G)

noncomputable def zcup (p q : ℕ) (x : cocycles A p) (y : cocycles B q) : cocycles (A ⊗ B) (p + q) :=
  cocyclesMk (cochainCup A B p q ((iCocycles A p).hom x) ((iCocycles B q).hom y)) (d_cup_eq_zero A B p q x y)

theorem i_zcup (p q : ℕ) (x : cocycles A p) (y : cocycles B q) :
    (iCocycles (A ⊗ B) (p + q)).hom (zcup A B p q x y)
      = cochainCup A B p q ((iCocycles A p).hom x) ((iCocycles B q).hom y) :=
  iCocycles_mk (cochainCup A B p q ((iCocycles A p).hom x) ((iCocycles B q).hom y)) (d_cup_eq_zero A B p q x y)

noncomputable def cupZ (p q : ℕ) : cocycles A p →ₗ[k] cocycles B q →ₗ[k] groupCohomology (A ⊗ B) (p + q) :=
  LinearMap.mk₂ k (fun x y => (groupCohomology.π (A ⊗ B) (p + q)).hom (zcup A B p q x y))
    (fun x x' y => by
      show (groupCohomology.π (A ⊗ B) (p + q)).hom (zcup A B p q (x + x') y)
        = (groupCohomology.π (A ⊗ B) (p + q)).hom (zcup A B p q x y)
          + (groupCohomology.π (A ⊗ B) (p + q)).hom (zcup A B p q x' y)
      rw [← map_add]
      exact congrArg _ (iCocycles_injective _ _ (by
        rw [map_add, i_zcup, i_zcup, i_zcup]; simp only [map_add, LinearMap.add_apply])))
    (fun c x y => by
      show (groupCohomology.π (A ⊗ B) (p + q)).hom (zcup A B p q (c • x) y)
        = c • (groupCohomology.π (A ⊗ B) (p + q)).hom (zcup A B p q x y)
      rw [← map_smul]
      exact congrArg _ (iCocycles_injective _ _ (by
        rw [map_smul, i_zcup, i_zcup]; simp only [map_smul, LinearMap.smul_apply])))
    (fun x y y' => by
      show (groupCohomology.π (A ⊗ B) (p + q)).hom (zcup A B p q x (y + y'))
        = (groupCohomology.π (A ⊗ B) (p + q)).hom (zcup A B p q x y)
          + (groupCohomology.π (A ⊗ B) (p + q)).hom (zcup A B p q x y')
      rw [← map_add]
      exact congrArg _ (iCocycles_injective _ _ (by
        rw [map_add, i_zcup, i_zcup, i_zcup]; simp only [map_add])))
    (fun c x y => by
      show (groupCohomology.π (A ⊗ B) (p + q)).hom (zcup A B p q x (c • y))
        = c • (groupCohomology.π (A ⊗ B) (p + q)).hom (zcup A B p q x y)
      rw [← map_smul]
      exact congrArg _ (iCocycles_injective _ _ (by
        rw [map_smul, i_zcup, i_zcup]; simp only [map_smul])))

theorem cupZ_apply (p q : ℕ) (x : cocycles A p) (y : cocycles B q) :
    cupZ A B p q x y = (groupCohomology.π (A ⊗ B) (p + q)).hom (zcup A B p q x y) := rfl

theorem cupZ_right_boundary (p q i : ℕ) (x : cocycles A p) (w : (inhomogeneousCochains B).X i) :
    cupZ A B p q x ((toCocycles B i q).hom w) = 0 := by
  by_cases hi : i + 1 = q
  · subst hi
    have key : zcup A B p (i + 1) x ((toCocycles B i (i + 1)).hom w)
        = ((-1 : k) ^ p) • (toCocycles (A ⊗ B) (p + i) (p + (i + 1))).hom
            (cochainCup A B p i ((iCocycles A p).hom x) w) := by
      apply iCocycles_injective
      rw [i_zcup, map_smul, i_toCocycles, i_toCocycles, d_cast B i (i + 1) rfl,
        d_cast (A ⊗ B) (p + i) (p + (i + 1)) rfl]
      funext σ
      simp only [Fin.cast_eq_self, Pi.smul_apply]
      rw [groupCohomology.d_cochainCup_apply, d_iCocycles, map_zero, LinearMap.zero_apply, Pi.zero_apply, zero_add,
        smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
    rw [cupZ_apply, key, map_smul, π_toCocycles, smul_zero]
  · rw [toCocycles_of_not_rel B i q hi]
    simp

theorem cupZ_left_boundary (p q i : ℕ) (w : (inhomogeneousCochains A).X i) (y : cocycles B q) :
    cupZ A B p q ((toCocycles A i p).hom w) y = 0 := by
  by_cases hi : i + 1 = p
  · subst hi
    have key : zcup A B (i + 1) q ((toCocycles A i (i + 1)).hom w) y
        = (toCocycles (A ⊗ B) (i + q) (i + 1 + q)).hom (cochainCup A B i q w ((iCocycles B q).hom y)) := by
      apply iCocycles_injective
      rw [i_zcup, i_toCocycles, i_toCocycles, d_cast A i (i + 1) rfl,
        d_cast (A ⊗ B) (i + q) (i + 1 + q) (Nat.add_right_comm i q 1)]
      funext σ
      simp only [Fin.cast_eq_self]
      rw [groupCohomology.d_cochainCup_apply, d_iCocycles, map_zero, Pi.zero_apply, smul_zero, add_zero]
      simp only [Fin.cast_cast, Fin.cast_eq_self]
    rw [cupZ_apply, key, π_toCocycles]
  · rw [toCocycles_of_not_rel A i p hi]
    simp

theorem cond_right (p q : ℕ) (x : cocycles A p) :
    toCocycles B ((ComplexShape.up ℕ).prev q) q ≫ ModuleCat.ofHom (cupZ A B p q x) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply]
  exact cupZ_right_boundary A B p q _ x w

noncomputable def cupZH (p q : ℕ) (x : cocycles A p) : groupCohomology B q ⟶ groupCohomology (A ⊗ B) (p + q) :=
  (Limits.CokernelCofork.IsColimit.desc' ((inhomogeneousCochains B).homologyIsCokernel _ q rfl)
    (ModuleCat.ofHom (cupZ A B p q x)) (cond_right A B p q x)).1

theorem π_cupZH (p q : ℕ) (x : cocycles A p) (y : cocycles B q) :
    (cupZH A B p q x).hom ((groupCohomology.π B q).hom y) = cupZ A B p q x y := by
  have := congrArg (fun φ => φ.hom y)
    (Limits.CokernelCofork.IsColimit.desc' ((inhomogeneousCochains B).homologyIsCokernel _ q rfl)
      (ModuleCat.ofHom (cupZ A B p q x)) (cond_right A B p q x)).2
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Limits.Cofork.π_ofπ] at this
  exact this

noncomputable def cupZHlin (p q : ℕ) :
    cocycles A p →ₗ[k] (groupCohomology B q →ₗ[k] groupCohomology (A ⊗ B) (p + q)) where
  toFun x := (cupZH A B p q x).hom
  map_add' x x' := by
    apply LinearMap.ext
    intro b
    obtain ⟨y, rfl⟩ := π_surjective B q b
    simp only [LinearMap.add_apply, π_cupZH, map_add]
  map_smul' c x := by
    apply LinearMap.ext
    intro b
    obtain ⟨y, rfl⟩ := π_surjective B q b
    simp only [LinearMap.smul_apply, π_cupZH, map_smul, RingHom.id_apply]

theorem cond_left (p q : ℕ) :
    toCocycles A ((ComplexShape.up ℕ).prev p) p ≫ ModuleCat.ofHom (cupZHlin A B p q) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  apply LinearMap.ext
  intro b
  obtain ⟨y, rfl⟩ := π_surjective B q b
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply]
  change (cupZH A B p q ((toCocycles A ((ComplexShape.up ℕ).prev p) p).hom w)).hom ((groupCohomology.π B q).hom y) = 0
  rw [π_cupZH]
  exact cupZ_left_boundary A B p q _ w y

noncomputable def cupHH (p q : ℕ) :
    groupCohomology A p ⟶ ModuleCat.of k (groupCohomology B q →ₗ[k] groupCohomology (A ⊗ B) (p + q)) :=
  (Limits.CokernelCofork.IsColimit.desc' ((inhomogeneousCochains A).homologyIsCokernel _ p rfl)
    (ModuleCat.ofHom (cupZHlin A B p q)) (cond_left A B p q)).1

theorem π_cupHH (p q : ℕ) (x : cocycles A p) :
    (cupHH A B p q).hom ((groupCohomology.π A p).hom x) = (cupZH A B p q x).hom := by
  have := congrArg (fun φ => φ.hom x)
    (Limits.CokernelCofork.IsColimit.desc' ((inhomogeneousCochains A).homologyIsCokernel _ p rfl)
      (ModuleCat.ofHom (cupZHlin A B p q)) (cond_left A B p q)).2
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Limits.Cofork.π_ofπ] at this
  exact this

noncomputable def cup : GradedCupFamily A B := fun p q => (cupHH A B p q).hom

theorem isGradedCupProduct_cup : IsGradedCupProduct A B (cup A B) where
  compat p q x y h := by
    show (cupHH A B p q).hom ((groupCohomology.π A p).hom x) ((groupCohomology.π B q).hom y) = _
    rw [π_cupHH, π_cupZH, cupZ_apply]
    rfl

end P2mS26CupE

theorem solution {k G : Type u} [CommRing k] [Group G] (A B : Rep.{u} k G) :
    ∃ cup : groupCohomology.GradedCupFamily A B, groupCohomology.IsGradedCupProduct A B cup := by
  exact ⟨P2mS26CupE.cup A B, P2mS26CupE.isGradedCupProduct_cup A B⟩

end S_groupCohomology_exists_isGradedCupProduct
end P2MW
export P2MW.S_groupCohomology_exists_isGradedCupProduct (solution)
