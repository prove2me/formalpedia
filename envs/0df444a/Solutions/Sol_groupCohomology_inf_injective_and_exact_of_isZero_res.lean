-- Prove2me | solution 1 for groupCohomology.inf_injective_and_exact_of_isZero_res
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/22913160-34ff-5480-9ece-33f92417f947

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_inf_injective_and_exact_of_isZero_res

set_option autoImplicit false
universe u
open CategoryTheory groupCohomology Rep
set_option maxHeartbeats 3200000

namespace P2mS26IR
open CategoryTheory

theorem shortExact_map_resFunctor {k G H : Type u} [CommRing k] [Group G] [Group H] (f : H →* G)
    {X : CategoryTheory.ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) :
    (X.map (Rep.resFunctor f)).ShortExact where
  exact := (forget₂ (Rep.{u} k H) (ModuleCat k)).reflects_exact_of_faithful _
    ((ShortComplex.moduleCat_exact_iff _).2 fun x hx => by
      have h := (hX.exact.map (forget₂ (Rep.{u} k G) (ModuleCat k))).moduleCat_range_eq_ker
      have hx' : x ∈ LinearMap.ker (ModuleCat.Hom.hom (X.map (forget₂ (Rep.{u} k G) (ModuleCat k))).g) := hx
      rw [← h] at hx'
      obtain ⟨a, ha⟩ := hx'
      exact ⟨a, ha⟩)
  mono_f := (Rep.mono_iff_injective _).2 ((Rep.mono_iff_injective X.f).1 hX.mono_f)
  epi_g := (Rep.epi_iff_surjective _).2 ((Rep.epi_iff_surjective X.g).1 hX.epi_g)

end P2mS26IR

noncomputable section
namespace P2mS26IR
open CategoryTheory CategoryTheory.Limits Representation

variable {k G : Type u} [CommRing k] [Group G]

theorem isZero_groupCohomology_coind_bot (B : Rep.{u} k (⊥ : Subgroup G)) (n : ℕ) :
    IsZero (groupCohomology (Rep.coind (⊥ : Subgroup G).subtype B) (n + 1)) :=
  IsZero.of_iso (isZero_groupCohomology_succ_of_subsingleton B n) (groupCohomology.coindIso B (n + 1))

lemma rho_bot_apply (B : Rep.{u} k (⊥ : Subgroup G)) (s : (⊥ : Subgroup G)) (b : B) : B.ρ s b = b := by
  rw [Subsingleton.elim s 1, map_one]; rfl

lemma mem_coindV_bot (B : Rep.{u} k (⊥ : Subgroup G)) (f : G → B) : f ∈ coindV (⊥ : Subgroup G).subtype B.ρ := by
  intro s x
  rw [rho_bot_apply, Subsingleton.elim s 1]
  show f (1 * x) = f x
  rw [one_mul]

lemma coind_apply_apply (B : Rep.{u} k (⊥ : Subgroup G)) (g x : G) (f : coindV (⊥ : Subgroup G).subtype B.ρ) :
    ((Representation.coind (⊥ : Subgroup G).subtype B.ρ g f : coindV (⊥ : Subgroup G).subtype B.ρ) : G → B) x
      = (f : G → B) (x * g) := rfl

section upshift
variable (A : Rep.{u} k G)

abbrev coindBot : Rep.{u} k G := Rep.coind (⊥ : Subgroup G).subtype (Rep.res (⊥ : Subgroup G).subtype A)

def iotaLin : A →ₗ[k] (coindBot A) where
  toFun a := ⟨fun x => A.ρ x a, mem_coindV_bot _ _⟩
  map_add' a b := by apply Subtype.ext; funext x; simp
  map_smul' c a := by apply Subtype.ext; funext x; simp

lemma iotaLin_apply (a : A) (x : G) : (((iotaLin A) a : coindV _ _) : G → A) x = A.ρ x a := rfl

def iota : A ⟶ (coindBot A) :=
  Rep.ofHom ⟨(iotaLin A), fun g => LinearMap.ext fun a => Subtype.ext (funext fun x => by
    show A.ρ x (A.ρ g a) = ((Representation.coind (⊥ : Subgroup G).subtype (Rep.res (⊥ : Subgroup G).subtype A).ρ g ((iotaLin A) a)
      : coindV _ _) : G → A) x
    rw [coind_apply_apply, iotaLin_apply, map_mul]; rfl)⟩

lemma iota_hom_apply (a : A) : (iota A).hom a = (iotaLin A) a := rfl

lemma iota_injective : Function.Injective (iota A).hom := fun a b h => by
  have := congrArg (fun f : (coindBot A) => (f : G → A) 1) h
  change ((iotaLin A a : coindV _ _) : G → A) 1 = ((iotaLin A b : coindV _ _) : G → A) 1 at this
  rw [iotaLin_apply, iotaLin_apply, map_one] at this
  exact this

abbrev upObj : Rep.{u} k G :=
  Rep.of (Representation.quotient (coindBot A).ρ (LinearMap.range (iota A).hom.toLinearMap) fun g => by
    rintro _ ⟨a, rfl⟩
    exact ⟨A.ρ g a, Rep.hom_comm_apply (iota A) g a⟩)

def proj : (coindBot A) ⟶ (upObj A) := Rep.ofHom ⟨Submodule.mkQ _, fun _ => rfl⟩

def upSeq : ShortComplex (Rep.{u} k G) where
  X₁ := A
  X₂ := (coindBot A)
  X₃ := (upObj A)
  f := (iota A)
  g := (proj A)
  zero := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun a =>
    (Submodule.Quotient.mk_eq_zero _).2 ⟨a, rfl⟩))

theorem upSeq_shortExact : ((upSeq A)).ShortExact where
  exact := (forget₂ (Rep.{u} k G) (ModuleCat k)).reflects_exact_of_faithful _ <|
    (ShortComplex.moduleCat_exact_iff _).2 fun (x : coindBot A) (hx : (proj A).hom x = 0) => by
      obtain ⟨a, ha⟩ : x ∈ LinearMap.range (iota A).hom.toLinearMap := (Submodule.Quotient.mk_eq_zero _).1 hx
      exact ⟨a, ha⟩
  mono_f := (Rep.mono_iff_injective _).2 (iota_injective A)
  epi_g := (Rep.epi_iff_surjective _).2 fun y =>
    Submodule.Quotient.induction_on (p := LinearMap.range (iota A).hom.toLinearMap) y fun x => ⟨x, rfl⟩

theorem isZero_groupCohomology_upSeq_X₂ (n : ℕ) : IsZero (groupCohomology ((upSeq A)).X₂ (n + 1)) :=
  isZero_groupCohomology_coind_bot _ n

end upshift
end P2mS26IR
end

noncomputable section
namespace P2mS26IR
open CategoryTheory CategoryTheory.Limits Representation

variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G)

section resIso
variable (B : Rep.{u} k (⊥ : Subgroup G))

abbrev cosetFun : Rep.{u} k (⊥ : Subgroup S) := Rep.trivial k (⊥ : Subgroup S) ((G ⧸ S) → B)

lemma rho_cosetFun (s : (⊥ : Subgroup S)) (F : (G ⧸ S) → B) : (cosetFun S B).ρ s F = F := rfl

def resToFun : coindV (⊥ : Subgroup G).subtype B.ρ →ₗ[k] coindV (⊥ : Subgroup S).subtype (cosetFun S B).ρ where
  toFun f := ⟨fun t q => (f : G → B) (Quotient.out q * (t : G)), fun s t => by
    rw [rho_cosetFun, Subsingleton.elim s 1]
    show (fun q => (f : G → B) (Quotient.out q * ((1 * t : S) : G))) = _
    rw [one_mul]
    rfl⟩
  map_add' f f' := by apply Subtype.ext; rfl
  map_smul' c f := by apply Subtype.ext; rfl

def cosetComp (x : G) : S := ⟨(Quotient.out (x : G ⧸ S))⁻¹ * x, QuotientGroup.leftRel_apply.1 (Quotient.exact' (QuotientGroup.out_eq' (x : G ⧸ S)))⟩

lemma out_mul_cosetComp (x : G) : Quotient.out (x : G ⧸ S) * (cosetComp S x : G) = x := by
  simp [cosetComp]

def funToRes : coindV (⊥ : Subgroup S).subtype (cosetFun S B).ρ →ₗ[k] coindV (⊥ : Subgroup G).subtype B.ρ where
  toFun F := ⟨fun x => ((F : S → (G ⧸ S) → B) (cosetComp S x)) (x : G ⧸ S), mem_coindV_bot B _⟩
  map_add' F F' := by apply Subtype.ext; rfl
  map_smul' c F := by apply Subtype.ext; rfl

lemma funToRes_resToFun (f : coindV (⊥ : Subgroup G).subtype B.ρ) : funToRes S B (resToFun S B f) = f := by
  apply Subtype.ext; funext x
  show (f : G → B) (Quotient.out (x : G ⧸ S) * (cosetComp S x : G)) = (f : G → B) x
  rw [out_mul_cosetComp]

lemma resToFun_funToRes (F : coindV (⊥ : Subgroup S).subtype (cosetFun S B).ρ) : resToFun S B (funToRes S B F) = F := by
  apply Subtype.ext; funext t q
  show ((F : S → (G ⧸ S) → B) (cosetComp S (Quotient.out q * (t : G)))) ((Quotient.out q * (t : G) : G) : G ⧸ S) = (F : S → (G ⧸ S) → B) t q
  have hq : ((Quotient.out q * (t : G) : G) : G ⧸ S) = q := by
    rw [QuotientGroup.mk_mul_of_mem _ t.2, QuotientGroup.out_eq']
  have ht : cosetComp S (Quotient.out q * (t : G)) = t := by
    apply Subtype.ext
    show (Quotient.out ((Quotient.out q * (t : G) : G) : G ⧸ S))⁻¹ * (Quotient.out q * (t : G)) = t
    rw [hq, inv_mul_cancel_left]
  rw [ht, hq]

def resEquiv : coindV (⊥ : Subgroup G).subtype B.ρ ≃ₗ[k] coindV (⊥ : Subgroup S).subtype (cosetFun S B).ρ :=
  LinearEquiv.ofLinear (resToFun S B) (funToRes S B) (LinearMap.ext (resToFun_funToRes S B)) (LinearMap.ext (funToRes_resToFun S B))

lemma resToFun_coind (t : S) (f : coindV (⊥ : Subgroup G).subtype B.ρ) :
    resToFun S B (Representation.coind (⊥ : Subgroup G).subtype B.ρ (t : G) f)
      = Representation.coind (⊥ : Subgroup S).subtype (cosetFun S B).ρ t (resToFun S B f) := by
  apply Subtype.ext; funext t' q
  show (f : G → B) (Quotient.out q * (t' : G) * (t : G)) = (f : G → B) (Quotient.out q * ((t' * t : S) : G))
  rw [Subgroup.coe_mul, mul_assoc]

def resIso : Rep.res S.subtype (Rep.coind (⊥ : Subgroup G).subtype B) ≅ Rep.coind (⊥ : Subgroup S).subtype (cosetFun S B) :=
  { hom := Rep.ofHom ⟨(resEquiv S B).toLinearMap, fun t => LinearMap.ext fun f => (resToFun_coind S B t f)⟩
    inv := Rep.ofHom ⟨(resEquiv S B).symm.toLinearMap, fun t => LinearMap.ext fun F => by
      apply (resEquiv S B).injective
      show resEquiv S B ((resEquiv S B).symm (Representation.coind (⊥ : Subgroup S).subtype (cosetFun S B).ρ t F))
        = resToFun S B (Representation.coind (⊥ : Subgroup G).subtype B.ρ (t : G) ((resEquiv S B).symm F))
      rw [LinearEquiv.apply_symm_apply, resToFun_coind]
      exact congrArg _ ((resEquiv S B).apply_symm_apply F).symm⟩
    hom_inv_id := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun f => (resEquiv S B).symm_apply_apply f))
    inv_hom_id := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun F => (resEquiv S B).apply_symm_apply F)) }

theorem isZero_groupCohomology_res_coind_bot (n : ℕ) :
    IsZero (groupCohomology (Rep.res S.subtype (Rep.coind (⊥ : Subgroup G).subtype B)) (n + 1)) :=
  IsZero.of_iso (isZero_groupCohomology_coind_bot _ n) ((groupCohomology.functor k S (n + 1)).mapIso (resIso S B))

end resIso
end P2mS26IR
end

noncomputable section
namespace P2mS26IR
open CategoryTheory CategoryTheory.Limits Representation

variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) [S.Normal]

section invIso
variable (B : Rep.{u} k (⊥ : Subgroup G))

abbrev quotTriv : Rep.{u} k (⊥ : Subgroup (G ⧸ S)) := Rep.trivial k (⊥ : Subgroup (G ⧸ S)) B

omit [S.Normal] in

lemma apply_eq_of_mem_invariants
    (x : invariants ((Representation.coind (⊥ : Subgroup G).subtype B.ρ).comp S.subtype))
    (a b : G) (hab : (a : G ⧸ S) = b) :
    ((x : coindV (⊥ : Subgroup G).subtype B.ρ) : G → B) a = ((x : coindV (⊥ : Subgroup G).subtype B.ρ) : G → B) b := by
  have hs : a⁻¹ * b ∈ S := QuotientGroup.leftRel_apply.1 (Quotient.exact' hab)
  have := x.2 ⟨a⁻¹ * b, hs⟩
  have := congrArg (fun f : coindV (⊥ : Subgroup G).subtype B.ρ => (f : G → B) a) this
  change ((x : coindV (⊥ : Subgroup G).subtype B.ρ) : G → B) (a * (a⁻¹ * b)) = _ at this
  rw [mul_inv_cancel_left] at this
  exact this.symm

lemma quotientToInvariants_mk_apply {V : Type u} [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (g : G) (x : invariants (ρ.comp S.subtype)) :
    ((ρ.quotientToInvariants S (QuotientGroup.mk g) x : invariants (ρ.comp S.subtype)) : V) = ρ g (x : V) := rfl

def invToFun : invariants ((Representation.coind (⊥ : Subgroup G).subtype B.ρ).comp S.subtype)
    →ₗ[k] coindV (⊥ : Subgroup (G ⧸ S)).subtype (quotTriv S B).ρ where
  toFun x := ⟨fun q => ((x : coindV (⊥ : Subgroup G).subtype B.ρ) : G → B) (Quotient.out q),
    mem_coindV_bot (G := G ⧸ S) (quotTriv S B) _⟩
  map_add' x y := by apply Subtype.ext; rfl
  map_smul' c x := by apply Subtype.ext; rfl

def funToInv : coindV (⊥ : Subgroup (G ⧸ S)).subtype (quotTriv S B).ρ
    →ₗ[k] invariants ((Representation.coind (⊥ : Subgroup G).subtype B.ρ).comp S.subtype) where
  toFun F := ⟨⟨fun g => (F : (G ⧸ S) → B) (g : G ⧸ S), mem_coindV_bot B _⟩, fun s => by
    apply Subtype.ext; funext g
    show (F : (G ⧸ S) → B) ((g * (s : G) : G) : G ⧸ S) = (F : (G ⧸ S) → B) (g : G ⧸ S)
    rw [QuotientGroup.mk_mul_of_mem _ s.2]⟩
  map_add' F F' := by apply Subtype.ext; apply Subtype.ext; rfl
  map_smul' c F := by apply Subtype.ext; apply Subtype.ext; rfl

lemma funToInv_invToFun (x) : funToInv S B (invToFun S B x) = x := by
  apply Subtype.ext; apply Subtype.ext; funext g
  show ((x : coindV (⊥ : Subgroup G).subtype B.ρ) : G → B) (Quotient.out (g : G ⧸ S)) = ((x : coindV (⊥ : Subgroup G).subtype B.ρ) : G → B) g
  exact apply_eq_of_mem_invariants S B x _ _ (QuotientGroup.out_eq' _)

lemma invToFun_funToInv (F) : invToFun S B (funToInv S B F) = F := by
  apply Subtype.ext; funext q
  show (F : (G ⧸ S) → B) ((Quotient.out q : G) : G ⧸ S) = (F : (G ⧸ S) → B) q
  rw [QuotientGroup.out_eq']

def invEquiv : invariants ((Representation.coind (⊥ : Subgroup G).subtype B.ρ).comp S.subtype)
    ≃ₗ[k] coindV (⊥ : Subgroup (G ⧸ S)).subtype (quotTriv S B).ρ :=
  LinearEquiv.ofLinear (invToFun S B) (funToInv S B) (LinearMap.ext (invToFun_funToInv S B)) (LinearMap.ext (funToInv_invToFun S B))

lemma invToFun_act (g : G) (x) :
    invToFun S B ((Representation.coind (⊥ : Subgroup G).subtype B.ρ).quotientToInvariants S (QuotientGroup.mk g) x)
      = Representation.coind (⊥ : Subgroup (G ⧸ S)).subtype (quotTriv S B).ρ (QuotientGroup.mk g) (invToFun S B x) := by
  apply Subtype.ext; funext q
  rw [coind_apply_apply]
  change ((((Representation.coind (⊥ : Subgroup G).subtype B.ρ).quotientToInvariants S (QuotientGroup.mk g) x : invariants ((Representation.coind (⊥ : Subgroup G).subtype B.ρ).comp S.subtype)) : coindV (⊥ : Subgroup G).subtype B.ρ) : G → B) (Quotient.out q) = ((x : coindV (⊥ : Subgroup G).subtype B.ρ) : G → B) (Quotient.out (q * QuotientGroup.mk g))
  rw [quotientToInvariants_mk_apply, coind_apply_apply]
  apply apply_eq_of_mem_invariants S B x
  rw [QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq']

def invIso : (Rep.coind (⊥ : Subgroup G).subtype B).quotientToInvariants S
    ≅ Rep.coind (⊥ : Subgroup (G ⧸ S)).subtype (quotTriv S B) :=
  { hom := Rep.ofHom ⟨(invEquiv S B).toLinearMap, fun q => by
      induction q using QuotientGroup.induction_on with | _ g =>
      exact LinearMap.ext fun x => invToFun_act S B g x⟩
    inv := Rep.ofHom ⟨(invEquiv S B).symm.toLinearMap, fun q => by
      induction q using QuotientGroup.induction_on with | _ g =>
      apply LinearMap.ext; intro F
      apply (invEquiv S B).injective
      show invEquiv S B ((invEquiv S B).symm (Representation.coind (⊥ : Subgroup (G ⧸ S)).subtype (quotTriv S B).ρ (QuotientGroup.mk g) F))
        = invToFun S B ((Representation.coind (⊥ : Subgroup G).subtype B.ρ).quotientToInvariants S (QuotientGroup.mk g) ((invEquiv S B).symm F))
      rw [LinearEquiv.apply_symm_apply, invToFun_act]
      exact congrArg _ ((invEquiv S B).apply_symm_apply F).symm⟩
    hom_inv_id := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => (invEquiv S B).symm_apply_apply x))
    inv_hom_id := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun F => (invEquiv S B).apply_symm_apply F)) }

theorem isZero_groupCohomology_quotientToInvariants_coind_bot (n : ℕ) :
    IsZero (groupCohomology ((Rep.coind (⊥ : Subgroup G).subtype B).quotientToInvariants S) (n + 1)) :=
  IsZero.of_iso (isZero_groupCohomology_coind_bot _ n) ((groupCohomology.functor k (G ⧸ S) (n + 1)).mapIso (invIso S B))

end invIso
end P2mS26IR
end

noncomputable section
namespace P2mS26IR
open CategoryTheory CategoryTheory.Limits Representation

variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) [S.Normal] (A : Rep.{u} k G)

lemma quotientToInvariantsFunctor_map_apply {X Y : Rep.{u} k G} (φ : X ⟶ Y) (x : invariants (X.ρ.comp S.subtype)) :
    (((Rep.quotientToInvariantsFunctor k S).map φ).hom x : invariants (Y.ρ.comp S.subtype)).1 = φ.hom x.1 := rfl

def invSeq : ShortComplex (Rep.{u} k (G ⧸ S)) where
  X₁ := A.quotientToInvariants S
  X₂ := (coindBot A).quotientToInvariants S
  X₃ := (upObj A).quotientToInvariants S
  f := (Rep.quotientToInvariantsFunctor k S).map (iota A)
  g := (Rep.quotientToInvariantsFunctor k S).map (proj A)
  zero := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => Subtype.ext
    ((Submodule.Quotient.mk_eq_zero _).2 ⟨x.1, rfl⟩)))

omit [S.Normal] in

lemma exists_of_cocycle (h1 : IsZero (groupCohomology (Rep.res S.subtype A) 1)) (c : S → A)
    (hc : ∀ s t : S, c (s * t) = A.ρ s (c t) + c s) : ∃ a : A, ∀ s : S, c s = A.ρ s a - a := by
  have hmem : c ∈ groupCohomology.cocycles₁ (Rep.res S.subtype A) :=
    (groupCohomology.mem_cocycles₁_iff (A := Rep.res S.subtype A) c).2 hc
  have hz : (groupCohomology.H1π (Rep.res S.subtype A)) ⟨c, hmem⟩ = 0 := by
    have : (𝟙 (groupCohomology.H1 (Rep.res S.subtype A)) : _ ⟶ _) = 0 := h1.eq_of_src _ _
    simpa using congrArg (fun φ : groupCohomology.H1 (Rep.res S.subtype A) ⟶ _ => φ.hom ((groupCohomology.H1π (Rep.res S.subtype A)) ⟨c, hmem⟩)) this
  rw [groupCohomology.H1π_eq_zero_iff] at hz
  obtain ⟨a, ha⟩ := hz
  refine ⟨a, fun s => ?_⟩
  have := congrFun ha s
  exact this.symm

theorem invSeq_shortExact (h1 : IsZero (groupCohomology (Rep.res S.subtype A) 1)) : (invSeq S A).ShortExact where
  mono_f := (Rep.mono_iff_injective _).2 fun x y h => by
    apply Subtype.ext
    apply iota_injective A
    have := congrArg (fun z : (coindBot A).quotientToInvariants S => (z : coindBot A)) h
    exact this
  epi_g := (Rep.epi_iff_surjective _).2 fun y => by

    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : coindBot A, (proj A).hom x₀ = y.1 :=
      Submodule.Quotient.induction_on (p := LinearMap.range (iota A).hom.toLinearMap) y.1 fun x => ⟨x, rfl⟩
    have hdef : ∀ s : S, ∃ a : A, (iota A).hom a = (coindBot A).ρ s x₀ - x₀ := fun s => by
      have hy := y.2 s
      have : (proj A).hom ((coindBot A).ρ s x₀ - x₀) = 0 := by
        rw [map_sub, Rep.hom_comm_apply, hx₀, sub_eq_zero]
        exact hy
      obtain ⟨a, ha⟩ : (coindBot A).ρ s x₀ - x₀ ∈ LinearMap.range (iota A).hom.toLinearMap :=
        (Submodule.Quotient.mk_eq_zero _).1 this
      exact ⟨a, ha⟩
    choose c hc using hdef
    have hcocy : ∀ s t : S, c (s * t) = A.ρ s (c t) + c s := fun s t => by
      apply iota_injective A
      rw [map_add, Rep.hom_comm_apply, hc, hc, hc]
      show (coindBot A).ρ ((s : G) * t) x₀ - x₀ = (coindBot A).ρ s ((coindBot A).ρ t x₀ - x₀) + ((coindBot A).ρ s x₀ - x₀)
      rw [map_mul, map_sub, Module.End.mul_apply]
      abel
    obtain ⟨a, ha⟩ := exists_of_cocycle S A h1 c hcocy
    have hinv : ∀ s : S, (coindBot A).ρ s (x₀ - (iota A).hom a) = x₀ - (iota A).hom a := fun s => by
      rw [map_sub, ← Rep.hom_comm_apply]
      have := hc s
      rw [ha s, map_sub] at this

      show (coindBot A).ρ s x₀ - (iota A).hom (A.ρ s a) = x₀ - (iota A).hom a
      rw [sub_eq_sub_iff_sub_eq_sub, ← this]
    refine ⟨⟨x₀ - (iota A).hom a, fun s => hinv s⟩, Subtype.ext ?_⟩
    change (proj A).hom (x₀ - (iota A).hom a) = y.1
    rw [map_sub, hx₀, sub_eq_self]
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨a, rfl⟩
  exact := (forget₂ (Rep.{u} k (G ⧸ S)) (ModuleCat k)).reflects_exact_of_faithful _ <|
    (ShortComplex.moduleCat_exact_iff _).2 fun (x : (coindBot A).quotientToInvariants S)
        (hx : ((Rep.quotientToInvariantsFunctor k S).map (proj A)).hom x = 0) => by
      have hx' : (proj A).hom (x : coindBot A) = 0 := by
        have := congrArg (fun z : (upObj A).quotientToInvariants S => (z : upObj A)) hx
        exact this
      obtain ⟨a, ha⟩ : (x : coindBot A) ∈ LinearMap.range (iota A).hom.toLinearMap := (Submodule.Quotient.mk_eq_zero _).1 hx'
      have hainv : ∀ s : S, A.ρ s a = a := fun s => by
        apply iota_injective A
        rw [Rep.hom_comm_apply, show (iota A).hom a = (x : coindBot A) from ha]
        exact x.2 s
      exact ⟨⟨a, fun s => hainv s⟩, Subtype.ext ha⟩

theorem isZero_groupCohomology_invSeq_X₂ (n : ℕ) : IsZero (groupCohomology (invSeq S A).X₂ (n + 1)) :=
  isZero_groupCohomology_quotientToInvariants_coind_bot S _ n

end P2mS26IR
end

noncomputable section
namespace P2mS26IR
open CategoryTheory CategoryTheory.Limits Representation

variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) [S.Normal] (A : Rep.{u} k G)

abbrev resSeq : ShortComplex (Rep.{u} k S) := (upSeq A).map (Rep.resFunctor S.subtype)

omit [S.Normal] in
theorem resSeq_shortExact : (resSeq S A).ShortExact := shortExact_map_resFunctor S.subtype (upSeq_shortExact A)

omit [S.Normal] in
theorem isZero_groupCohomology_resSeq_X₂ (n : ℕ) : IsZero (groupCohomology (resSeq S A).X₂ (n + 1)) :=
  isZero_groupCohomology_res_coind_bot S _ n

abbrev inf (X : Rep.{u} k G) (n : ℕ) : groupCohomology (X.quotientToInvariants S) n ⟶ groupCohomology X n :=
  groupCohomology.map (A := X.quotientToInvariants S) (B := X) (QuotientGroup.mk' S) (Rep.ofHom (X.ρ.quotientToInvariants_lift S)) n

private abbrev _root_.P2mS26IR.res (X : Rep.{u} k G) (n : ℕ) : groupCohomology X n ⟶ groupCohomology (Rep.res S.subtype X) n :=
  groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype X)) n

p2m_export "P2mS26IR" "res"

def infHom : (invSeq S A).map (groupCohomology.cochainsFunctor k (G ⧸ S)) ⟶ (upSeq A).map (groupCohomology.cochainsFunctor k G) where
  τ₁ := groupCohomology.cochainsMap (A := A.quotientToInvariants S) (B := A) (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S))
  τ₂ := groupCohomology.cochainsMap (A := (coindBot A).quotientToInvariants S) (B := coindBot A) (QuotientGroup.mk' S)
    (Rep.ofHom ((coindBot A).ρ.quotientToInvariants_lift S))
  τ₃ := groupCohomology.cochainsMap (A := (upObj A).quotientToInvariants S) (B := upObj A) (QuotientGroup.mk' S)
    (Rep.ofHom ((upObj A).ρ.quotientToInvariants_lift S))
  comm₁₂ := by
    apply HomologicalComplex.hom_ext
    intro i
    simp only [HomologicalComplex.comp_f, ShortComplex.map_f, groupCohomology.cochainsMap_f]
    rfl
  comm₂₃ := by
    apply HomologicalComplex.hom_ext
    intro i
    simp only [HomologicalComplex.comp_f, ShortComplex.map_g, groupCohomology.cochainsMap_f]
    rfl

def resHom : (upSeq A).map (groupCohomology.cochainsFunctor k G) ⟶ (resSeq S A).map (groupCohomology.cochainsFunctor k S) where
  τ₁ := groupCohomology.cochainsMap S.subtype (𝟙 (Rep.res S.subtype A))
  τ₂ := groupCohomology.cochainsMap S.subtype (𝟙 (Rep.res S.subtype (coindBot A)))
  τ₃ := groupCohomology.cochainsMap S.subtype (𝟙 (Rep.res S.subtype (upObj A)))
  comm₁₂ := by
    apply HomologicalComplex.hom_ext
    intro i
    simp only [HomologicalComplex.comp_f, ShortComplex.map_f, groupCohomology.cochainsMap_f]
    rfl
  comm₂₃ := by
    apply HomologicalComplex.hom_ext
    intro i
    simp only [HomologicalComplex.comp_f, ShortComplex.map_g, groupCohomology.cochainsMap_f]
    rfl

theorem delta_inf (h1 : IsZero (groupCohomology (Rep.res S.subtype A) 1)) (i j : ℕ) (hij : i + 1 = j) :
    groupCohomology.δ (invSeq_shortExact S A h1) i j hij ≫ inf S A j
      = inf S (upObj A) i ≫ groupCohomology.δ (upSeq_shortExact A) i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality (infHom S A)
    (groupCohomology.map_cochainsFunctor_shortExact (invSeq_shortExact S A h1))
    (groupCohomology.map_cochainsFunctor_shortExact (upSeq_shortExact A)) i j hij

omit [S.Normal] in

theorem delta_res (i j : ℕ) (hij : i + 1 = j) :
    groupCohomology.δ (upSeq_shortExact A) i j hij ≫ res S A j
      = res S (upObj A) i ≫ groupCohomology.δ (resSeq_shortExact S A) i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality (resHom S A)
    (groupCohomology.map_cochainsFunctor_shortExact (upSeq_shortExact A))
    (groupCohomology.map_cochainsFunctor_shortExact (resSeq_shortExact S A)) i j hij

end P2mS26IR
end

noncomputable section
namespace P2mS26IR
open CategoryTheory CategoryTheory.Limits Representation

variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) [S.Normal]

def P (q : ℕ) (A : Rep.{u} k G) : Prop :=
  Function.Injective (inf S A q).hom ∧
    ∀ x : groupCohomology A q, (res S A q).hom x = 0 → ∃ y, (inf S A q).hom y = x

theorem map_degree_zero_injective {H : Type u} [Group H] {X : Rep.{u} k H} {Y : Rep.{u} k G}
    (f : G →* H) (φ : Rep.res f X ⟶ Y) (hφ : Function.Injective (Rep.Hom.hom φ).toLinearMap) :
    Function.Injective (groupCohomology.map f φ 0).hom := by
  intro a b hab
  have ha := groupCohomology.map_H0Iso_hom_f_apply f φ a
  have hb := groupCohomology.map_H0Iso_hom_f_apply f φ b
  have h2 := congrArg (fun t => (groupCohomology.shortComplexH0 Y).f.hom ((groupCohomology.H0Iso Y).hom.hom t)) hab
  have h3 := ha.symm.trans (h2.trans hb)

  have h4 : (groupCohomology.shortComplexH0 X).f.hom ((groupCohomology.H0Iso X).hom.hom a)
      = (groupCohomology.shortComplexH0 X).f.hom ((groupCohomology.H0Iso X).hom.hom b) := hφ h3
  have h5 : (groupCohomology.H0Iso X).hom.hom a = (groupCohomology.H0Iso X).hom.hom b := by
    rw [groupCohomology.shortComplexH0_f] at h4
    exact Subtype.ext h4
  exact (ModuleCat.mono_iff_injective (groupCohomology.H0Iso X).hom).1 inferInstance h5

theorem base_zero (A : Rep.{u} k G) :
    Function.Injective (inf S A 0).hom ∧
    ∀ x : groupCohomology A 0, (res S A 0).hom x = 0 → ∃ y, (inf S A 0).hom y = x := by
  refine ⟨map_degree_zero_injective (QuotientGroup.mk' S) _ (fun a b h => Subtype.ext h), fun x hx => ⟨0, ?_⟩⟩
  have hres : Function.Injective (res S A 0).hom :=
    map_degree_zero_injective S.subtype (𝟙 (Rep.res S.subtype A)) (fun a b h => h)
  rw [map_zero]
  exact (hres (hx.trans (map_zero _).symm)).symm

theorem base_one (A : Rep.{u} k G) :
    Function.Injective (inf S A 1).hom ∧
    ∀ x : groupCohomology A 1, (res S A 1).hom x = 0 → ∃ y, (inf S A 1).hom y = x := by
  constructor
  · exact (ModuleCat.mono_iff_injective _).1 (groupCohomology.instMonoModuleCatFH1InfRes A S)
  · intro x hx
    exact (ShortComplex.moduleCat_exact_iff _).1 (groupCohomology.H1InfRes_exact A S) x hx

lemma eq_zero_of_isZero {M : ModuleCat.{u} k} (h : IsZero M) (x : M) : x = 0 := by
  simpa using congrArg (fun φ : M ⟶ M => φ.hom x) (h.eq_of_src (𝟙 _) 0)

lemma comp_apply_eq {X Y Y' Z : ModuleCat.{u} k} {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X ⟶ Y'} {g' : Y' ⟶ Z} (h : f ≫ g = f' ≫ g') (x : X) :
    g.hom (f.hom x) = g'.hom (f'.hom x) := by
  simpa using congrArg (fun φ : X ⟶ Z => φ.hom x) h

theorem step (q : ℕ) (hq : 1 ≤ q) (A : Rep.{u} k G)
    (h1 : IsZero (groupCohomology (Rep.res S.subtype A) 1)) (hP : P S q (upObj A)) : P S (q + 1) A := by
  obtain ⟨hinjQ, hexQ⟩ := hP

  have eq_q : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  obtain ⟨m, rfl⟩ := eq_q
  haveI iY : IsIso (groupCohomology.δ (upSeq_shortExact A) (m + 1) (m + 1 + 1) rfl) :=
    groupCohomology.isIso_δ_of_isZero _ _ (isZero_groupCohomology_upSeq_X₂ A m) (isZero_groupCohomology_upSeq_X₂ A (m + 1))
  haveI iYS : IsIso (groupCohomology.δ (invSeq_shortExact S A h1) (m + 1) (m + 1 + 1) rfl) :=
    groupCohomology.isIso_δ_of_isZero _ _ (isZero_groupCohomology_invSeq_X₂ S A m) (isZero_groupCohomology_invSeq_X₂ S A (m + 1))
  haveI iYR : IsIso (groupCohomology.δ (resSeq_shortExact S A) (m + 1) (m + 1 + 1) rfl) :=
    groupCohomology.isIso_δ_of_isZero _ _ (isZero_groupCohomology_resSeq_X₂ S A m) (isZero_groupCohomology_resSeq_X₂ S A (m + 1))
  let eY := (asIso (groupCohomology.δ (upSeq_shortExact A) (m + 1) (m + 1 + 1) rfl)).toLinearEquiv
  let eYS := (asIso (groupCohomology.δ (invSeq_shortExact S A h1) (m + 1) (m + 1 + 1) rfl)).toLinearEquiv
  let eYR := (asIso (groupCohomology.δ (resSeq_shortExact S A) (m + 1) (m + 1 + 1) rfl)).toLinearEquiv
  have sq_inf := fun y => comp_apply_eq (delta_inf S A h1 (m + 1) (m + 1 + 1) rfl) y
  have sq_res := fun x => comp_apply_eq (delta_res S A (m + 1) (m + 1 + 1) rfl) x
  refine ⟨?_, ?_⟩
  ·
    intro y₁ y₂ h
    obtain ⟨z₁, rfl⟩ := eYS.surjective y₁
    obtain ⟨z₂, rfl⟩ := eYS.surjective y₂
    have h' : (groupCohomology.δ (upSeq_shortExact A) (m + 1) (m + 1 + 1) rfl).hom ((inf S (upObj A) (m + 1)).hom z₁)
        = (groupCohomology.δ (upSeq_shortExact A) (m + 1) (m + 1 + 1) rfl).hom ((inf S (upObj A) (m + 1)).hom z₂) :=
      (sq_inf z₁).symm.trans (h.trans (sq_inf z₂))
    rw [hinjQ (eY.injective h')]
  ·
    intro x hx
    obtain ⟨x', rfl⟩ := eY.surjective x
    have hres : (res S (upObj A) (m + 1)).hom x' = 0 := by
      apply eYR.injective
      exact ((sq_res x').symm.trans hx).trans eYR.map_zero.symm
    obtain ⟨y', hy'⟩ := hexQ x' hres
    exact ⟨eYS y', (sq_inf y').trans (congrArg _ hy')⟩

theorem main (q : ℕ) : ∀ (A : Rep.{u} k G),
    (∀ i : ℕ, 1 ≤ i → i < q → IsZero (groupCohomology (Rep.res S.subtype A) i)) → P S q A := by
  rcases Nat.lt_or_ge q 1 with hq | hq
  · obtain rfl : q = 0 := by omega
    exact fun A _ => base_zero S A
  · induction q, hq using Nat.le_induction with
    | base => exact fun A _ => base_one S A
    | succ q hq ih =>
      intro A hvan
      have h1 : IsZero (groupCohomology (Rep.res S.subtype A) 1) := hvan 1 le_rfl (by omega)
      apply step S q hq A h1
      apply ih
      intro i hi hiq

      have hiso : IsIso (groupCohomology.δ (resSeq_shortExact S A) i (i + 1) rfl) := by
        obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        exact groupCohomology.isIso_δ_of_isZero _ _ (isZero_groupCohomology_resSeq_X₂ S A j) (isZero_groupCohomology_resSeq_X₂ S A (j + 1))
      exact IsZero.of_iso (hvan (i + 1) (by omega) (by omega))
        (@asIso _ _ _ _ (groupCohomology.δ (resSeq_shortExact S A) i (i + 1) rfl) hiso)

end P2mS26IR
end

theorem solution
    {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (S : Subgroup G) [S.Normal] (q : ℕ)
    (hvan : ∀ i : ℕ, 1 ≤ i → i < q → CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype A) i)) :
    Function.Injective (groupCohomology.map (A := A.quotientToInvariants S) (B := A)
        (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) q).hom ∧
    ∀ x : groupCohomology A q, (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) q).hom x = 0 →
      ∃ y : groupCohomology (A.quotientToInvariants S) q,
        (groupCohomology.map (A := A.quotientToInvariants S) (B := A)
        (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) q).hom y = x :=
  P2mS26IR.main S q A hvan

end S_groupCohomology_inf_injective_and_exact_of_isZero_res
end P2MW
export P2MW.S_groupCohomology_inf_injective_and_exact_of_isZero_res (solution)
