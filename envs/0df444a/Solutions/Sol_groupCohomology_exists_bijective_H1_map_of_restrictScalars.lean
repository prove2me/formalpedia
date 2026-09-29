-- Prove2me | solution 1 for groupCohomology.exists_bijective_H1_map_of_restrictScalars
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/759df6e9-6115-58fa-b9fd-f7d9a7299202

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_bijective_H1_map_of_restrictScalars

set_option autoImplicit false

open CategoryTheory groupCohomology

universe u

namespace P2mK4NRes

variable {k K : Type u} [Field k] [Field K]
variable {G : Type u} [Group G]

theorem H1π_surjective' {R : Type u} [CommRing R] (B : Rep R G) (x : H1 B) :
    ∃ c : cocycles₁ B, H1π B c = x :=
  H1_induction_on x (fun c => ⟨c, rfl⟩)

variable {V : Type u} [AddCommGroup V] [Module K V] [Module k V]
variable (ρ : Representation K G V) (ρ₀ : Representation k G V)
variable (hρ : ∀ g v, ρ₀ g v = ρ g v)

local notation "A" => Rep.of ρ
local notation "A₀" => Rep.of ρ₀

include hρ

theorem mem_cocycles₁_iff_of_restrict (f : G → V) :
    f ∈ cocycles₁ (Rep.of ρ₀) ↔ f ∈ cocycles₁ (Rep.of ρ) := by
  rw [mem_cocycles₁_iff, mem_cocycles₁_iff]
  constructor
  · intro h g h'
    rw [← hρ]; exact h g h'
  · intro h g h'
    rw [hρ]; exact h g h'

theorem mem_coboundaries₁_iff_of_restrict (f : G → V) :
    f ∈ coboundaries₁ (Rep.of ρ₀) ↔ f ∈ coboundaries₁ (Rep.of ρ) := by
  simp only [coboundaries₁, LinearMap.mem_range]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    funext g
    have := congrFun hm g
    rw [d₀₁_hom_apply] at this ⊢
    rw [← hρ]; exact this
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    funext g
    have := congrFun hm g
    rw [d₀₁_hom_apply] at this ⊢
    rw [hρ]; exact this

def toK (c : cocycles₁ (Rep.of ρ₀)) : cocycles₁ (Rep.of ρ) :=
  ⟨(c : G → V), (mem_cocycles₁_iff_of_restrict ρ ρ₀ hρ c).mp c.2⟩

def fromK (c : cocycles₁ (Rep.of ρ)) : cocycles₁ (Rep.of ρ₀) :=
  ⟨(c : G → V), (mem_cocycles₁_iff_of_restrict ρ ρ₀ hρ c).mpr c.2⟩

@[scoped simp] theorem coe_toK (c : cocycles₁ (Rep.of ρ₀)) : ((toK ρ ρ₀ hρ c : cocycles₁ (Rep.of ρ)) : G → V) = c := rfl
@[scoped simp] theorem coe_fromK (c : cocycles₁ (Rep.of ρ)) : ((fromK ρ ρ₀ hρ c : cocycles₁ (Rep.of ρ₀)) : G → V) = c := rfl

theorem toK_add (c d : cocycles₁ (Rep.of ρ₀)) : toK ρ ρ₀ hρ (c + d) = toK ρ ρ₀ hρ c + toK ρ ρ₀ hρ d := by
  apply Subtype.ext; rfl

theorem H1π_toK_eq_of_eq (c d : cocycles₁ (Rep.of ρ₀))
    (h : H1π (Rep.of ρ₀) c = H1π (Rep.of ρ₀) d) :
    H1π (Rep.of ρ) (toK ρ ρ₀ hρ c) = H1π (Rep.of ρ) (toK ρ ρ₀ hρ d) := by
  rw [H1π_eq_iff] at h ⊢
  exact (mem_coboundaries₁_iff_of_restrict ρ ρ₀ hρ _).mp h

variable [Algebra k K] [IsScalarTower k K V]

theorem toK_smul (a : k) (c : cocycles₁ (Rep.of ρ₀)) :
    toK ρ ρ₀ hρ (a • c) = algebraMap k K a • toK ρ ρ₀ hρ c := by
  apply Subtype.ext
  funext g
  change (a • (c : G → V)) g = (algebraMap k K a • ((c : G → V))) g
  simp only [Pi.smul_apply, algebraMap_smul]

noncomputable def PsiFun (x : H1 (Rep.of ρ₀)) : H1 (Rep.of ρ) :=
  H1π (Rep.of ρ) (toK ρ ρ₀ hρ (Classical.choose (H1π_surjective' (Rep.of ρ₀) x)))

theorem PsiFun_H1π (c : cocycles₁ (Rep.of ρ₀)) :
    PsiFun ρ ρ₀ hρ (H1π (Rep.of ρ₀) c) = H1π (Rep.of ρ) (toK ρ ρ₀ hρ c) := by
  unfold PsiFun
  apply H1π_toK_eq_of_eq
  exact Classical.choose_spec (H1π_surjective' (Rep.of ρ₀) (H1π (Rep.of ρ₀) c))

noncomputable def Psi : H1 (Rep.of ρ₀) →ₛₗ[algebraMap k K] H1 (Rep.of ρ) where
  toFun := PsiFun ρ ρ₀ hρ
  map_add' x y := by
    obtain ⟨c, rfl⟩ := H1π_surjective' (Rep.of ρ₀) x
    obtain ⟨d, rfl⟩ := H1π_surjective' (Rep.of ρ₀) y
    rw [← map_add, PsiFun_H1π, PsiFun_H1π, PsiFun_H1π, toK_add, map_add]
  map_smul' a x := by
    obtain ⟨c, rfl⟩ := H1π_surjective' (Rep.of ρ₀) x
    rw [← map_smul, PsiFun_H1π, PsiFun_H1π, toK_smul, map_smul]

theorem Psi_H1π (c : cocycles₁ (Rep.of ρ₀)) :
    Psi ρ ρ₀ hρ (H1π (Rep.of ρ₀) c) = H1π (Rep.of ρ) (toK ρ ρ₀ hρ c) :=
  PsiFun_H1π ρ ρ₀ hρ c

theorem Psi_H1π_of_coe_eq (c₀ : cocycles₁ (Rep.of ρ₀)) (c : cocycles₁ (Rep.of ρ))
    (h : (c₀ : G → V) = c) :
    Psi ρ ρ₀ hρ (H1π (Rep.of ρ₀) c₀) = H1π (Rep.of ρ) c := by
  rw [Psi_H1π]
  congr 1
  exact Subtype.ext h

theorem Psi_injective : Function.Injective (Psi ρ ρ₀ hρ) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨c, rfl⟩ := H1π_surjective' (Rep.of ρ₀) x
  rw [Psi_H1π, H1π_eq_zero_iff] at hx
  rw [H1π_eq_zero_iff]
  exact (mem_coboundaries₁_iff_of_restrict ρ ρ₀ hρ _).mpr hx

theorem Psi_surjective : Function.Surjective (Psi ρ ρ₀ hρ) := by
  intro y
  obtain ⟨c, rfl⟩ := H1π_surjective' (Rep.of ρ) y
  exact ⟨H1π (Rep.of ρ₀) (fromK ρ ρ₀ hρ c), Psi_H1π_of_coe_eq ρ ρ₀ hρ _ _ rfl⟩

theorem finrank_comap_Psi [FiniteDimensional k K] (X : Submodule K (H1 (Rep.of ρ))) :
    Module.finrank k (X.comap (Psi ρ ρ₀ hρ)) = Module.finrank k K * Module.finrank K X := by

  letI instk : Module k X := Module.compHom X (algebraMap k K)
  have hsmul : ∀ (a : k) (y : X), a • y = algebraMap k K a • y := fun _ _ => rfl
  haveI : IsScalarTower k K X :=
    ⟨fun a b y => by rw [hsmul, Algebra.smul_def, mul_smul]⟩

  let e : X.comap (Psi ρ ρ₀ hρ) →ₗ[k] X :=
    { toFun := fun x => (⟨Psi ρ ρ₀ hρ x, x.2⟩ : X)
      map_add' := fun x y => by
        apply Subtype.ext
        change Psi ρ ρ₀ hρ (x + y : H1 (Rep.of ρ₀)) = Psi ρ ρ₀ hρ x + Psi ρ ρ₀ hρ y
        rw [map_add]
      map_smul' := fun a x => by
        apply Subtype.ext
        rw [RingHom.id_apply, hsmul]
        change Psi ρ ρ₀ hρ (a • (x : H1 (Rep.of ρ₀))) = algebraMap k K a • Psi ρ ρ₀ hρ x
        rw [LinearMap.map_smulₛₗ] }
  have he : Function.Bijective e := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      have := congrArg (fun z : X => (z : H1 (Rep.of ρ))) hxy
      exact Psi_injective ρ ρ₀ hρ this
    · intro y
      obtain ⟨x, hx⟩ := Psi_surjective ρ ρ₀ hρ (y : H1 (Rep.of ρ))
      refine ⟨⟨x, ?_⟩, ?_⟩
      · change Psi ρ ρ₀ hρ x ∈ X
        rw [hx]; exact y.2
      · apply Subtype.ext
        exact hx
  rw [(LinearEquiv.ofBijective e he).finrank_eq, Module.finrank_mul_finrank]

theorem main :
    ∃ Ψ : H1 (Rep.of ρ₀) →ₛₗ[algebraMap k K] H1 (Rep.of ρ),
      Function.Bijective Ψ ∧
      (∀ (c₀ : cocycles₁ (Rep.of ρ₀)) (c : cocycles₁ (Rep.of ρ)), (c₀ : G → V) = c →
        Ψ (H1π (Rep.of ρ₀) c₀) = H1π (Rep.of ρ) c) ∧
      (∀ [FiniteDimensional k K], ∀ X : Submodule K (H1 (Rep.of ρ)),
        Module.finrank k (X.comap Ψ) = Module.finrank k K * Module.finrank K X) :=
  ⟨Psi ρ ρ₀ hρ, ⟨Psi_injective ρ ρ₀ hρ, Psi_surjective ρ ρ₀ hρ⟩, Psi_H1π_of_coe_eq ρ ρ₀ hρ,
    fun X => finrank_comap_Psi ρ ρ₀ hρ X⟩

end P2mK4NRes
p2m_reactivate "P2MW.S_groupCohomology_exists_bijective_H1_map_of_restrictScalars.P2mK4NRes"

theorem solution
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : Type u} [Group G]
    {V : Type u} [AddCommGroup V] [Module K V] [Module k V] [IsScalarTower k K V]
    (ρ : Representation K G V) (ρ₀ : Representation k G V)
    (hρ : ∀ g v, ρ₀ g v = ρ g v) :
    ∃ Ψ : H1 (Rep.of ρ₀) →ₛₗ[algebraMap k K] H1 (Rep.of ρ),
      Function.Bijective Ψ ∧
      (∀ (c₀ : cocycles₁ (Rep.of ρ₀)) (c : cocycles₁ (Rep.of ρ)), (c₀ : G → V) = c →
        Ψ (H1π (Rep.of ρ₀) c₀) = H1π (Rep.of ρ) c) ∧
      (∀ [FiniteDimensional k K], ∀ X : Submodule K (H1 (Rep.of ρ)),
        Module.finrank k (X.comap Ψ) = Module.finrank k K * Module.finrank K X) :=
  P2mK4NRes.main ρ ρ₀ hρ

end S_groupCohomology_exists_bijective_H1_map_of_restrictScalars
end P2MW
export P2MW.S_groupCohomology_exists_bijective_H1_map_of_restrictScalars (solution)
