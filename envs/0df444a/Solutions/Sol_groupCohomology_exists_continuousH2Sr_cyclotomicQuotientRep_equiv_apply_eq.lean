-- Prove2me | solution 1 for groupCohomology.exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/718852b2-cdcf-592d-b831-2ee32f951c44

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_Rep_QuotientRightTranslation
import Definitions.Def_GroupCohomology_CyclotomicQuotientH2Rep
import Theorems.Thm_IntermediateField_IsUnramifiedOutside_normalClosure
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation"
set_option maxHeartbeats 800000
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open CategoryTheory groupCohomology ExtCitation

namespace SH2

variable {G : Type} [Group G] (Λ : Subgroup G) [Λ.Normal]

structure Transversal where
  σ : G ⧸ Λ → G
  mk_σ : ∀ q, (σ q : G ⧸ Λ) = q
  σ_one : σ 1 = 1

namespace Transversal

variable {Λ}

lemma nonempty : Nonempty (Transversal Λ) := by
  classical
  refine ⟨⟨Function.update Quotient.out 1 1, fun q => ?_, Function.update_self _ _ _⟩⟩
  by_cases hq : q = 1
  · subst hq; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne hq]; exact q.out_eq

variable (τ : Transversal Λ)

abbrev qinv (x : G) : G ⧸ Λ := ((x⁻¹ : G) : G ⧸ Λ)

lemma lam_mem (x : G) : x * τ.σ (qinv (Λ := Λ) x) ∈ Λ := by
  have h : ((τ.σ (qinv (Λ := Λ) x) : G) : G ⧸ Λ) = ((x⁻¹ : G) : G ⧸ Λ) := τ.mk_σ _
  rw [QuotientGroup.eq] at h
  have := Λ.inv_mem h
  rwa [mul_inv_rev, inv_inv, inv_inv] at this

def lam (x : G) : Λ := ⟨x * τ.σ (qinv (Λ := Λ) x), τ.lam_mem x⟩

@[scoped simp] lemma coe_lam (x : G) : (τ.lam x : G) = x * τ.σ (qinv (Λ := Λ) x) := rfl

lemma lam_mul_σ_inv (x : G) : (τ.lam x : G) * (τ.σ (qinv (Λ := Λ) x))⁻¹ = x := by
  rw [coe_lam, mul_inv_cancel_right]

lemma qinv_eq_of_eq {y : G} {μ : G} (hμ : μ ∈ Λ) {q : G ⧸ Λ} (h : y = μ * (τ.σ q)⁻¹) : qinv (Λ := Λ) y = q := by
  rw [qinv, ← τ.mk_σ q, QuotientGroup.eq, inv_inv, h, mul_assoc, inv_mul_cancel, mul_one]
  exact hμ

lemma coe_lam_eq_of_eq {y : G} {μ : G} (hμ : μ ∈ Λ) {q : G ⧸ Λ} (h : y = μ * (τ.σ q)⁻¹) : (τ.lam y : G) = μ := by
  rw [coe_lam, τ.qinv_eq_of_eq hμ h, h, inv_mul_cancel_right]

lemma coe_lam_of_mem {s : G} (hs : s ∈ Λ) : (τ.lam s : G) = s :=
  τ.coe_lam_eq_of_eq hs (q := 1) (by rw [τ.σ_one, inv_one, mul_one])

lemma coe_lam_σ_inv (q : G ⧸ Λ) : (τ.lam (τ.σ q)⁻¹ : G) = 1 :=
  τ.coe_lam_eq_of_eq Λ.one_mem (by rw [one_mul])

lemma qinv_σ_inv (q : G ⧸ Λ) : qinv (Λ := Λ) (τ.σ q)⁻¹ = q :=
  τ.qinv_eq_of_eq Λ.one_mem (by rw [one_mul])

lemma coe_lam_mul (x g : G) :
    (τ.lam (x * g) : G) = τ.lam x * τ.lam ((τ.σ (qinv (Λ := Λ) x))⁻¹ * g) := by
  apply τ.coe_lam_eq_of_eq (Λ.mul_mem (τ.lam x).2 (τ.lam _).2) (q := qinv (Λ := Λ) ((τ.σ (qinv (Λ := Λ) x))⁻¹ * g))
  conv_lhs => rw [← τ.lam_mul_σ_inv x, mul_assoc, ← τ.lam_mul_σ_inv ((τ.σ (qinv (Λ := Λ) x))⁻¹ * g)]
  rw [mul_assoc]

lemma qinv_mul (x g : G) :
    qinv (Λ := Λ) (x * g) = qinv (Λ := Λ) ((τ.σ (qinv (Λ := Λ) x))⁻¹ * g) := by
  apply τ.qinv_eq_of_eq (Λ.mul_mem (τ.lam x).2 (τ.lam _).2)
  conv_lhs => rw [← τ.lam_mul_σ_inv x, mul_assoc, ← τ.lam_mul_σ_inv ((τ.σ (qinv (Λ := Λ) x))⁻¹ * g)]
  rw [mul_assoc]

lemma qinv_mul_of_mem (x u : G) (hu : u ∈ Λ) : qinv (Λ := Λ) (x * u) = qinv (Λ := Λ) x := by
  rw [qinv, qinv, QuotientGroup.eq, inv_inv]
  exact Subgroup.Normal.conj_mem inferInstance u hu x

lemma coe_lam_mul_of_mem (x u : G) (hu : u ∈ Λ) :
    (τ.lam (x * u) : G) = τ.lam x * ((τ.σ (qinv (Λ := Λ) x))⁻¹ * u * τ.σ (qinv (Λ := Λ) x)) := by
  rw [coe_lam, coe_lam, qinv_mul_of_mem x u hu]
  group

lemma coe_lam_mul_left_of_mem (μ y : G) (hμ : μ ∈ Λ) : (τ.lam (μ * y) : G) = μ * τ.lam y := by
  apply τ.coe_lam_eq_of_eq (Λ.mul_mem hμ (τ.lam y).2) (q := qinv (Λ := Λ) y)
  rw [mul_assoc, τ.lam_mul_σ_inv]

end Transversal
p2m_reactivate "P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2.Transversal"

end SH2
p2m_reactivate "P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2.Transversal P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2"

noncomputable section
namespace SH2

open scoped TensorProduct

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L)

abbrev Λ : Subgroup ↥K.fixingSubgroup := L.fixingSubgroup.subgroupOf K.fixingSubgroup

abbrev incl : ↥L.fixingSubgroup →* ↥K.fixingSubgroup := Subgroup.inclusion (IntermediateField.fixingSubgroup_antitone hKL)

lemma incl_level (s : ↥L.fixingSubgroup) : K.fixingSubgroup.subtype (incl K L hKL s) = L.fixingSubgroup.subtype s := rfl

lemma incl_mem (s : ↥L.fixingSubgroup) : incl K L hKL s ∈ Λ K L := Subgroup.mem_subgroupOf.2 s.2

variable [(Λ K L).Normal]

lemma smul_quotient_eq_mul (g : ↥K.fixingSubgroup) (q : ↥K.fixingSubgroup ⧸ Λ K L) : g • q = (g : ↥K.fixingSubgroup ⧸ Λ K L) * q := by
  induction q using QuotientGroup.induction_on with
  | H a => rfl

lemma mk_incl (s : ↥L.fixingSubgroup) : (incl K L hKL s : ↥K.fixingSubgroup ⧸ Λ K L) = 1 := by
  rw [QuotientGroup.eq_one_iff]; exact incl_mem K L hKL s

def toH (g : ↥K.fixingSubgroup) (hg : g ∈ Λ K L) : ↥L.fixingSubgroup := ⟨g, Subgroup.mem_subgroupOf.1 hg⟩

@[scoped simp] lemma incl_toH (g : ↥K.fixingSubgroup) (hg : g ∈ Λ K L) : incl K L hKL (toH K L g hg) = g := Subtype.ext rfl
@[scoped simp] lemma coe_toH (g : ↥K.fixingSubgroup) (hg : g ∈ Λ K L) : ((toH K L g hg : ↥L.fixingSubgroup) : Γ) = (g : Γ) := rfl
@[scoped simp] lemma toH_incl (s : ↥L.fixingSubgroup) : toH K L (incl K L hKL s) (incl_mem K L hKL s) = s := Subtype.ext rfl

lemma toH_mul (g g' : ↥K.fixingSubgroup) (hg : g ∈ Λ K L) (hg' : g' ∈ Λ K L) :
    toH K L (g * g') (Subgroup.mul_mem _ hg hg') = toH K L g hg * toH K L g' hg' := Subtype.ext rfl

lemma toH_inv (g : ↥K.fixingSubgroup) (hg : g ∈ Λ K L) :
    toH K L g⁻¹ (Subgroup.inv_mem _ hg) = (toH K L g hg)⁻¹ := Subtype.ext rfl

variable (p)

abbrev χK : ↥K.fixingSubgroup →* (ZMod p)ˣ := (cycloChar p).comp K.fixingSubgroup.subtype
abbrev χL : ↥L.fixingSubgroup →* (ZMod p)ˣ := (cycloChar p).comp L.fixingSubgroup.subtype

lemma χL_eq (s : ↥L.fixingSubgroup) : χL p L s = χK p K (incl K L hKL s) := rfl
lemma χK_toH (g : ↥K.fixingSubgroup) (hg : g ∈ Λ K L) : χL p L (toH K L g hg) = χK p K g := rfl

abbrev A : Rep.{0} (ZMod p) ↥K.fixingSubgroup :=
  (Rep.ofMulActionFinsupp (ZMod p) ↥K.fixingSubgroup (↥K.fixingSubgroup ⧸ Λ K L)).twist (χK p K)
abbrev B : Rep.{0} (ZMod p) ↥L.fixingSubgroup := (Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist (χL p L)

lemma A_ρ_apply_apply (g : ↥K.fixingSubgroup) (f : ↥K.fixingSubgroup ⧸ Λ K L →₀ ZMod p) (q : ↥K.fixingSubgroup ⧸ Λ K L) :
    (A p K L).ρ g f q = (χK p K g : ZMod p) * f ((g : ↥K.fixingSubgroup ⧸ Λ K L)⁻¹ * q) := by
  change ((Rep.ofMulActionFinsupp (ZMod p) ↥K.fixingSubgroup (↥K.fixingSubgroup ⧸ Λ K L)).ρ.twist (χK p K)) g f q = _
  rw [Representation.twist_apply_apply, Finsupp.smul_apply, smul_eq_mul]
  congr 1
  change Representation.ofMulActionFinsupp (ZMod p) ↥K.fixingSubgroup (↥K.fixingSubgroup ⧸ Λ K L) g f q = _
  rw [Representation.ofMulActionFinsupp_apply, smul_quotient_eq_mul, QuotientGroup.mk_inv]

lemma A_ρ_apply_apply' (g : ↥K.fixingSubgroup) (f : ↥K.fixingSubgroup ⧸ Λ K L →₀ ZMod p) (q : ↥K.fixingSubgroup ⧸ Λ K L) :
    ((Representation.ofMulActionFinsupp (ZMod p) ↥K.fixingSubgroup (↥K.fixingSubgroup ⧸ Λ K L)).twist (χK p K)) g f q =
      (χK p K g : ZMod p) * f ((g : ↥K.fixingSubgroup ⧸ Λ K L)⁻¹ * q) :=
  A_ρ_apply_apply p K L g f q

lemma B_ρ_apply (s : ↥L.fixingSubgroup) (t : ZMod p) : (B p L).ρ s t = (χL p L s : ZMod p) * t := rfl
lemma B_ρ_apply' (s : ↥L.fixingSubgroup) (t : ZMod p) :
    ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).ρ.twist (χL p L)) s t = (χL p L s : ZMod p) * t := rfl

abbrev pr₁ : A p K L →ₗ[ZMod p] B p L := Finsupp.lapply (1 : ↥K.fixingSubgroup ⧸ Λ K L)

lemma hpr (s : ↥L.fixingSubgroup) (x : A p K L) : pr₁ p K L ((A p K L).ρ (incl K L hKL s) x) = (B p L).ρ s (pr₁ p K L x) := by
  change (A p K L).ρ (incl K L hKL s) x 1 = (χL p L s : ZMod p) * x 1
  rw [A_ρ_apply_apply, mk_incl, inv_one, one_mul]
  rfl

noncomputable abbrev sh : continuousH2Sr K.fixingSubgroup.subtype S (A p K L) →ₗ[ZMod p] continuousH2Sr L.fixingSubgroup.subtype S (B p L) :=
  continuousH2SrMap (incl K L hKL) (incl_level K L hKL) S (pr₁ p K L) (hpr p K L hKL)

end SH2
p2m_reactivate "P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2.Transversal P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2"
end
p2m_reactivate "P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2.Transversal P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2"

noncomputable section
namespace SH2

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L)
variable [(Λ K L).Normal] [(Λ K L).FiniteIndex] (τ : Transversal (Λ K L))

def lamH (x : ↥K.fixingSubgroup) : ↥L.fixingSubgroup := toH K L (τ.lam x) (τ.lam x).2

lemma coe_lamH (x : ↥K.fixingSubgroup) : ((lamH K L τ x : ↥L.fixingSubgroup) : Γ) = ((τ.lam x : ↥K.fixingSubgroup) : Γ) := rfl

lemma incl_lamH (x : ↥K.fixingSubgroup) : incl K L hKL (lamH K L τ x) = τ.lam x := Subtype.ext rfl

lemma lamH_eq_mul_of {x y z : ↥K.fixingSubgroup} (h : (τ.lam x : ↥K.fixingSubgroup) = τ.lam y * τ.lam z) :
    lamH K L τ x = lamH K L τ y * lamH K L τ z := by
  apply Subtype.ext
  change ((τ.lam x : ↥K.fixingSubgroup) : Γ) = ((τ.lam y : ↥K.fixingSubgroup) : Γ) * ((τ.lam z : ↥K.fixingSubgroup) : Γ)
  rw [h]; rfl

lemma lamH_mul (y h : ↥K.fixingSubgroup) :
    lamH K L τ (y * h) = lamH K L τ y * lamH K L τ ((τ.σ (Transversal.qinv y))⁻¹ * h) :=
  lamH_eq_mul_of K L τ (τ.coe_lam_mul y h)

lemma lamH_of_mem (s : ↥L.fixingSubgroup) : lamH K L τ (incl K L hKL s) = s := by
  apply Subtype.ext
  change ((τ.lam (incl K L hKL s) : ↥K.fixingSubgroup) : Γ) = (s : Γ)
  rw [τ.coe_lam_of_mem (incl_mem K L hKL s)]; rfl

variable (p)

def ψfun (w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) :
    ↥K.fixingSubgroup × ↥K.fixingSubgroup → (↥K.fixingSubgroup ⧸ Λ K L →₀ ZMod p) := fun gg =>
  Finsupp.equivFunOnFinite.symm fun q =>
    (χK p K (τ.σ q) : ZMod p) *
      w (lamH K L τ ((τ.σ q)⁻¹ * gg.1), (lamH K L τ ((τ.σ q)⁻¹ * gg.1))⁻¹ * lamH K L τ ((τ.σ q)⁻¹ * gg.1 * gg.2))

lemma ψfun_apply (w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) (g₁ g₂ : ↥K.fixingSubgroup) (q : ↥K.fixingSubgroup ⧸ Λ K L) :
    ψfun p K L τ w (g₁, g₂) q = (χK p K (τ.σ q) : ZMod p) *
      w (lamH K L τ ((τ.σ q)⁻¹ * g₁), (lamH K L τ ((τ.σ q)⁻¹ * g₁))⁻¹ * lamH K L τ ((τ.σ q)⁻¹ * g₁ * g₂)) := by
  simp [ψfun]

lemma ψfun_add (w w' : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) : ψfun p K L τ (w + w') = ψfun p K L τ w + ψfun p K L τ w' := by
  funext gg; apply Finsupp.ext; intro q
  obtain ⟨g₁, g₂⟩ := gg
  simp only [Pi.add_apply, Finsupp.add_apply, ψfun_apply, mul_add]

lemma ψfun_smul (a : ZMod p) (w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) : ψfun p K L τ (a • w) = a • ψfun p K L τ w := by
  funext gg; apply Finsupp.ext; intro q
  obtain ⟨g₁, g₂⟩ := gg
  simp only [Pi.smul_apply, Finsupp.smul_apply, ψfun_apply, smul_eq_mul]
  ring

lemma qinv_σ_inv_mul (q : ↥K.fixingSubgroup ⧸ Λ K L) (g : ↥K.fixingSubgroup) :
    Transversal.qinv ((τ.σ q)⁻¹ * g) = (g : ↥K.fixingSubgroup ⧸ Λ K L)⁻¹ * q := by
  rw [Transversal.qinv, mul_inv_rev, inv_inv, QuotientGroup.mk_mul, QuotientGroup.mk_inv, τ.mk_σ]

lemma ψfun_mem_cocycles₂ {w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p} (hw : w ∈ cocycles₂ (B p L)) :
    ψfun p K L τ w ∈ cocycles₂ (A p K L) := by
  rw [mem_cocycles₂_iff] at hw ⊢
  intro g h j
  apply Finsupp.ext
  intro q
  simp only [Finsupp.add_apply, A_ρ_apply_apply', ψfun_apply]

  set q' : ↥K.fixingSubgroup ⧸ Λ K L := (g : ↥K.fixingSubgroup ⧸ Λ K L)⁻¹ * q with hq'
  set x : ↥K.fixingSubgroup := (τ.σ q)⁻¹ with hx
  set x' : ↥K.fixingSubgroup := (τ.σ q')⁻¹ with hx'
  have hσ : (τ.σ (Transversal.qinv (x * g)))⁻¹ = x' := by rw [hx, qinv_σ_inv_mul, ← hq']

  have hab : lamH K L τ (x * g * h) = lamH K L τ (x * g) * lamH K L τ (x' * h) := by
    rw [lamH_mul K L τ (x * g) h, hσ]
  have habc : lamH K L τ (x * g * (h * j)) = lamH K L τ (x * g) * lamH K L τ (x' * h * j) := by
    rw [lamH_mul K L τ (x * g) (h * j), hσ, mul_assoc]
  have hbc : lamH K L τ (x' * h * j) =
      lamH K L τ (x' * h) * lamH K L τ ((τ.σ (Transversal.qinv (x' * h)))⁻¹ * j) := lamH_mul K L τ (x' * h) j

  have hχ : (χK p K g : ZMod p) * (χK p K (τ.σ q') : ZMod p) =
      (χK p K (τ.σ q) : ZMod p) * (χL p L (lamH K L τ (x * g)) : ZMod p) := by
    have h1 := τ.lam_mul_σ_inv (x * g)
    rw [hσ] at h1

    have h1' : g * τ.σ q' = τ.σ q * (τ.lam (x * g) : ↥K.fixingSubgroup) := by
      calc g * τ.σ q' = τ.σ q * (x * g) * τ.σ q' := by rw [hx]; group
        _ = τ.σ q * ((τ.lam (x * g) : ↥K.fixingSubgroup) * x') * τ.σ q' := by rw [h1]
        _ = τ.σ q * (τ.lam (x * g) : ↥K.fixingSubgroup) := by rw [hx']; group
    have h2 := congrArg (fun y => ((χK p K y : (ZMod p)ˣ) : ZMod p)) h1'
    simp only [map_mul, Units.val_mul] at h2
    exact h2

  rw [show x * (g * h) = x * g * h from (mul_assoc _ _ _).symm, show x * g * h * j = x * g * (h * j) from mul_assoc _ _ _,
    hab, habc, hbc]
  simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  have hw' := hw (lamH K L τ (x * g)) (lamH K L τ (x' * h)) (lamH K L τ ((τ.σ (Transversal.qinv (x' * h)))⁻¹ * j))
  rw [B_ρ_apply'] at hw'
  linear_combination (χK p K (τ.σ q) : ZMod p) * hw' -
    w (lamH K L τ (x' * h), lamH K L τ ((τ.σ (Transversal.qinv (x' * h)))⁻¹ * j)) * hχ

end SH2
p2m_reactivate "P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2.Transversal P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2"
end
p2m_reactivate "P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2.Transversal P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2"

noncomputable section
namespace SH2

local instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance normalQbar : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

local notation "Qbar" => (AlgebraicClosure ℚ)
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

lemma conj_mem_fixingSubgroup (E : IntermediateField ℚ Qbar) [Normal ℚ E] {s : Γ} (hs : s ∈ E.fixingSubgroup) (x : Γ) :
    x * s * x⁻¹ ∈ E.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff] at hs ⊢
  intro y hy
  have hle := IntermediateField.normal_iff_forall_map_le'.mp (inferInstance : Normal ℚ E) x⁻¹
  have hy' : x⁻¹ y ∈ E := hle ⟨y, hy, rfl⟩
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hs _ hy']
  simp

lemma exists_deep_level {S : Finset Nat.Primes} {F L : IntermediateField ℚ Qbar} (hF : F.IsUnramifiedOutside S)
    (hL : L.IsUnramifiedOutside S) :
    ∃ N : IntermediateField ℚ Qbar, N.IsUnramifiedOutside S ∧ N.fixingSubgroup ≤ F.fixingSubgroup ∧
      N.fixingSubgroup ≤ L.fixingSubgroup ∧ ∀ (s : Γ), s ∈ N.fixingSubgroup → ∀ x : Γ, x⁻¹ * s * x ∈ N.fixingSubgroup := by
  have hFL := hF.sup hL
  haveI : FiniteDimensional ℚ ↥(F ⊔ L) := hFL.1
  have hle : (IntermediateField.normalClosure ℚ (↥(F ⊔ L)) Qbar).fixingSubgroup ≤ (F ⊔ L).fixingSubgroup :=
    IntermediateField.fixingSubgroup_antitone (IntermediateField.le_normalClosure (F ⊔ L))
  refine ⟨IntermediateField.normalClosure ℚ (↥(F ⊔ L)) Qbar, IntermediateField.IsUnramifiedOutside.normalClosure hFL,
    hle.trans (IntermediateField.fixingSubgroup_antitone le_sup_left),
    hle.trans (IntermediateField.fixingSubgroup_antitone le_sup_right), fun s hs x => ?_⟩
  haveI : Normal ℚ ↥(IntermediateField.normalClosure ℚ (↥(F ⊔ L)) Qbar) := normalClosure.normal ℚ (↥(F ⊔ L)) Qbar
  have := conj_mem_fixingSubgroup (IntermediateField.normalClosure ℚ (↥(F ⊔ L)) Qbar) hs x⁻¹
  rwa [inv_inv] at this

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (K L : IntermediateField ℚ Qbar) (hKL : K ≤ L)
variable [(Λ K L).Normal] [(Λ K L).FiniteIndex] (τ : Transversal (Λ K L))

section CocycleB
variable (p) {w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p} (hw : w ∈ cocycles₂ (B p L))
include hw

lemma w_one_left (c : ↥L.fixingSubgroup) : w (1, c) = w (1, 1) := by
  have h := (mem_cocycles₂_iff _).1 hw 1 1 c
  rw [B_ρ_apply', one_mul, one_mul, map_one, Units.val_one, one_mul] at h
  linear_combination -h

lemma w_one_right (a : ↥L.fixingSubgroup) : w (a, 1) = (χL p L a : ZMod p) * w (1, 1) := by
  have h := (mem_cocycles₂_iff _).1 hw a 1 1
  rw [B_ρ_apply', mul_one, mul_one] at h
  linear_combination h

lemma w_left_deep (P : ↥L.fixingSubgroup → Prop) (hP1 : P 1)
    (hwr : ∀ (g g' s s' : ↥L.fixingSubgroup), P s → P s' → w (g * s, g' * s') = w (g, g'))
    (a c u : ↥L.fixingSubgroup) (hu : P u) : w (a, u * c) = w (a, c) := by
  have h := (mem_cocycles₂_iff _).1 hw a u c
  rw [B_ρ_apply'] at h
  have h1 : w (a * u, c) = w (a, c) := by simpa using hwr a c u 1 hu hP1
  have h2 : w (a, u) = w (a, 1) := by simpa using hwr a 1 1 u hP1 hu
  have h3 : w (u, c) = w (1, c) := by simpa using hwr 1 c u 1 hu hP1
  rw [h1, h2, h3, w_one_left p L hw, w_one_right p L hw] at h
  linear_combination -h

end CocycleB
p2m_reactivate "P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2.Transversal P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2"

variable (p)

lemma ψfun_isLevelConstantSr₂ (hL : L.IsUnramifiedOutside S) {w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p}
    (hw : w ∈ levelCocyclesSr₂ L.fixingSubgroup.subtype S (B p L)) :
    IsLevelConstantSr₂ K.fixingSubgroup.subtype S (ψfun p K L τ w) := by
  obtain ⟨hwc, F, hF, hwF⟩ := hw
  obtain ⟨N, hN, hNF, hNL, hconj⟩ := exists_deep_level hF hL
  refine ⟨N, hN, fun g g' u u' hu hu' => ?_⟩

  have hdeepΛ : ∀ y : ↥K.fixingSubgroup, (y : Γ) ∈ N.fixingSubgroup → y ∈ Λ K L :=
    fun y hy => Subgroup.mem_subgroupOf.2 (hNL hy)
  have hdeepconj : ∀ (y x : ↥K.fixingSubgroup), (y : Γ) ∈ N.fixingSubgroup → ((x⁻¹ * y * x : ↥K.fixingSubgroup) : Γ) ∈ N.fixingSubgroup :=
    fun y x hy => hconj _ hy _
  change ((u : ↥K.fixingSubgroup) : Γ) ∈ N.fixingSubgroup at hu
  change ((u' : ↥K.fixingSubgroup) : Γ) ∈ N.fixingSubgroup at hu'
  apply Finsupp.ext
  intro q
  rw [ψfun_apply, ψfun_apply]
  congr 1
  set x : ↥K.fixingSubgroup := (τ.σ q)⁻¹ with hx

  set c : ↥K.fixingSubgroup := τ.σ (Transversal.qinv (x * g)) with hc
  have huu : ((c⁻¹ * u * c : ↥K.fixingSubgroup) : Γ) ∈ N.fixingSubgroup := hdeepconj u c hu
  have h1 : lamH K L τ (x * (g * u)) = lamH K L τ (x * g) * toH K L (c⁻¹ * u * c) (hdeepΛ _ huu) := by
    apply Subtype.ext
    change ((τ.lam (x * (g * u)) : ↥K.fixingSubgroup) : Γ) = ((τ.lam (x * g) : ↥K.fixingSubgroup) : Γ) * ((c⁻¹ * u * c : ↥K.fixingSubgroup) : Γ)
    rw [← mul_assoc, τ.coe_lam_mul_of_mem (x * g) u (hdeepΛ u hu)]
    rfl

  set v : ↥K.fixingSubgroup := g'⁻¹ * u * g' * u' with hv
  have hvN : ((v : ↥K.fixingSubgroup) : Γ) ∈ N.fixingSubgroup := by
    rw [hv, Subgroup.coe_mul]
    exact N.fixingSubgroup.mul_mem (hdeepconj u g' hu) hu'
  set c' : ↥K.fixingSubgroup := τ.σ (Transversal.qinv (x * g * g')) with hc'
  have hvv : ((c'⁻¹ * v * c' : ↥K.fixingSubgroup) : Γ) ∈ N.fixingSubgroup := hdeepconj v c' hvN
  have h2 : lamH K L τ (x * (g * u) * (g' * u')) = lamH K L τ (x * g * g') * toH K L (c'⁻¹ * v * c') (hdeepΛ _ hvv) := by
    apply Subtype.ext
    change ((τ.lam (x * (g * u) * (g' * u')) : ↥K.fixingSubgroup) : Γ) =
      ((τ.lam (x * g * g') : ↥K.fixingSubgroup) : Γ) * ((c'⁻¹ * v * c' : ↥K.fixingSubgroup) : Γ)
    rw [show x * (g * u) * (g' * u') = x * g * g' * v by rw [hv]; group, τ.coe_lam_mul_of_mem (x * g * g') v (hdeepΛ v hvN)]
    rfl
  rw [h1, h2]

  set a := lamH K L τ (x * g)
  set Y := lamH K L τ (x * g * g')
  set uu := toH K L (c⁻¹ * u * c) (hdeepΛ _ huu)
  set vv := toH K L (c'⁻¹ * v * c') (hdeepΛ _ hvv)
  have huuF : ((uu : ↥L.fixingSubgroup) : Γ) ∈ F.fixingSubgroup := hNF huu
  have hvvF : ((vv : ↥L.fixingSubgroup) : Γ) ∈ F.fixingSubgroup := hNF hvv
  have hwr : ∀ (g g' s s' : ↥L.fixingSubgroup), (s : Γ) ∈ F.fixingSubgroup → (s' : Γ) ∈ F.fixingSubgroup →
      w (g * s, g' * s') = w (g, g') := fun g g' s s' hs hs' => hwF g g' s s' hs hs'
  rw [show (a * uu)⁻¹ * (Y * vv) = uu⁻¹ * (a⁻¹ * Y) * vv by group, hwr a (uu⁻¹ * (a⁻¹ * Y)) uu vv huuF hvvF]
  exact w_left_deep p L hwc (fun s => (s : Γ) ∈ F.fixingSubgroup) F.fixingSubgroup.one_mem hwr a (a⁻¹ * Y) uu⁻¹
    (F.fixingSubgroup.inv_mem huuF)

include τ in
theorem sh_surjective (hL : L.IsUnramifiedOutside S) : Function.Surjective (sh p S K L hKL) := by
  intro y
  obtain ⟨w, rfl⟩ := continuousH2Srπ_surjective _ S _ y
  let z : ↥(levelCocyclesSr₂ K.fixingSubgroup.subtype S (A p K L)) :=
    ⟨ψfun p K L τ w.1, ⟨ψfun_mem_cocycles₂ p K L τ w.2.1, ψfun_isLevelConstantSr₂ p S K L τ hL w.2⟩⟩
  refine ⟨continuousH2Srπ _ S _ z, ?_⟩
  rw [continuousH2SrMap_continuousH2Srπ]
  congr 1
  apply Subtype.ext
  funext st
  obtain ⟨s, t⟩ := st
  rw [coe_levelCocyclesSr₂Map, cochainsPullPush₂_apply]
  change ψfun p K L τ w.1 (incl K L hKL s, incl K L hKL t) 1 = w.1 (s, t)
  rw [ψfun_apply, τ.σ_one, inv_one, one_mul, map_one, Units.val_one, one_mul, ← map_mul,
    lamH_of_mem K L hKL, lamH_of_mem K L hKL, inv_mul_cancel_left]

end SH2
p2m_reactivate "P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2.Transversal P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2"
end
p2m_reactivate "P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2.Transversal P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2"

noncomputable section
namespace SH2

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L)
variable [(Λ K L).Normal] [(Λ K L).FiniteIndex] (τ : Transversal (Λ K L))

variable (p)

abbrev shF : (↥K.fixingSubgroup × ↥K.fixingSubgroup → A p K L) →ₗ[ZMod p] (↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) :=
  cochainsPullPush₂ (incl K L hKL) (pr₁ p K L)

lemma shF_apply (z : ↥K.fixingSubgroup × ↥K.fixingSubgroup → A p K L) (s t : ↥L.fixingSubgroup) :
    shF p K L hKL z (s, t) = z (incl K L hKL s, incl K L hKL t) 1 := rfl

lemma ψfun_incl_incl_one (w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) (s t : ↥L.fixingSubgroup) :
    ψfun p K L τ w (incl K L hKL s, incl K L hKL t) 1 = w (s, t) := by
  rw [ψfun_apply, τ.σ_one, inv_one, one_mul, map_one, Units.val_one, one_mul, ← map_mul,
    lamH_of_mem K L hKL, lamH_of_mem K L hKL, inv_mul_cancel_left]

lemma shF_ψfun (w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) : shF p K L hKL (ψfun p K L τ w) = w := by
  funext st; obtain ⟨s, t⟩ := st; exact ψfun_incl_incl_one p K L hKL τ w s t

def ψ₁ (y : ↥L.fixingSubgroup → ZMod p) : ↥K.fixingSubgroup → A p K L := fun g =>
  Finsupp.equivFunOnFinite.symm fun q => (χK p K (τ.σ q) : ZMod p) * y (lamH K L τ ((τ.σ q)⁻¹ * g))

lemma ψ₁_apply (y : ↥L.fixingSubgroup → ZMod p) (g : ↥K.fixingSubgroup) (q : ↥K.fixingSubgroup ⧸ Λ K L) :
    ψ₁ p K L τ y g q = (χK p K (τ.σ q) : ZMod p) * y (lamH K L τ ((τ.σ q)⁻¹ * g)) := by
  simp [ψ₁]

lemma χ_bookkeeping (q : ↥K.fixingSubgroup ⧸ Λ K L) (g : ↥K.fixingSubgroup) :
    (χK p K g : ZMod p) * (χK p K (τ.σ ((g : ↥K.fixingSubgroup ⧸ Λ K L)⁻¹ * q)) : ZMod p) =
      (χK p K (τ.σ q) : ZMod p) * (χL p L (lamH K L τ ((τ.σ q)⁻¹ * g)) : ZMod p) := by
  set q' := (g : ↥K.fixingSubgroup ⧸ Λ K L)⁻¹ * q with hq'
  have hσ : (τ.σ (Transversal.qinv ((τ.σ q)⁻¹ * g)))⁻¹ = (τ.σ q')⁻¹ := by rw [qinv_σ_inv_mul, ← hq']
  have h1 := τ.lam_mul_σ_inv ((τ.σ q)⁻¹ * g)
  rw [hσ] at h1
  have h1' : g * τ.σ q' = τ.σ q * (τ.lam ((τ.σ q)⁻¹ * g) : ↥K.fixingSubgroup) := by
    calc g * τ.σ q' = τ.σ q * ((τ.σ q)⁻¹ * g) * τ.σ q' := by group
      _ = τ.σ q * ((τ.lam ((τ.σ q)⁻¹ * g) : ↥K.fixingSubgroup) * (τ.σ q')⁻¹) * τ.σ q' := by rw [h1]
      _ = τ.σ q * (τ.lam ((τ.σ q)⁻¹ * g) : ↥K.fixingSubgroup) := by group
  have h2 := congrArg (fun y => ((χK p K y : (ZMod p)ˣ) : ZMod p)) h1'
  simp only [map_mul, Units.val_mul] at h2
  exact h2

lemma g_mul_σ (q : ↥K.fixingSubgroup ⧸ Λ K L) (g : ↥K.fixingSubgroup) :
    g * τ.σ ((g : ↥K.fixingSubgroup ⧸ Λ K L)⁻¹ * q) = τ.σ q * (τ.lam ((τ.σ q)⁻¹ * g) : ↥K.fixingSubgroup) := by
  set q' := (g : ↥K.fixingSubgroup ⧸ Λ K L)⁻¹ * q with hq'
  have hσ : (τ.σ (Transversal.qinv ((τ.σ q)⁻¹ * g)))⁻¹ = (τ.σ q')⁻¹ := by rw [qinv_σ_inv_mul, ← hq']
  have h1 := τ.lam_mul_σ_inv ((τ.σ q)⁻¹ * g)
  rw [hσ] at h1
  calc g * τ.σ q' = τ.σ q * ((τ.σ q)⁻¹ * g) * τ.σ q' := by group
    _ = τ.σ q * ((τ.lam ((τ.σ q)⁻¹ * g) : ↥K.fixingSubgroup) * (τ.σ q')⁻¹) * τ.σ q' := by rw [h1]
    _ = τ.σ q * (τ.lam ((τ.σ q)⁻¹ * g) : ↥K.fixingSubgroup) := by group

lemma ψfun_d₁₂ (y : ↥L.fixingSubgroup → ZMod p) :
    ψfun p K L τ ((d₁₂ (B p L)).hom y) = (d₁₂ (A p K L)).hom (ψ₁ p K L τ y) := by
  funext gg
  obtain ⟨g, h⟩ := gg
  apply Finsupp.ext
  intro q
  rw [ψfun_apply, d₁₂_hom_apply, d₁₂_hom_apply, B_ρ_apply', Finsupp.add_apply, Finsupp.sub_apply,
    A_ρ_apply_apply', ψ₁_apply, ψ₁_apply, ψ₁_apply]
  set q' : ↥K.fixingSubgroup ⧸ Λ K L := (g : ↥K.fixingSubgroup ⧸ Λ K L)⁻¹ * q with hq'
  set x : ↥K.fixingSubgroup := (τ.σ q)⁻¹ with hx
  set x' : ↥K.fixingSubgroup := (τ.σ q')⁻¹ with hx'
  have hσ : (τ.σ (Transversal.qinv (x * g)))⁻¹ = x' := by rw [hx, qinv_σ_inv_mul, ← hq']
  have hab : lamH K L τ (x * g * h) = lamH K L τ (x * g) * lamH K L τ (x' * h) := by
    rw [lamH_mul K L τ (x * g) h, hσ]
  have hχ := χ_bookkeeping p K L τ q g
  rw [← hq', ← hx] at hχ
  rw [show x * (g * h) = x * g * h from (mul_assoc _ _ _).symm, hab, inv_mul_cancel_left]
  linear_combination -(y (lamH K L τ (x' * h))) * hχ

end SH2
p2m_reactivate "P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2.Transversal P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2"
end
p2m_reactivate "P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2.Transversal P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2"

noncomputable section
namespace SH2

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L)
variable [(Λ K L).Normal] [(Λ K L).FiniteIndex] (τ : Transversal (Λ K L))
variable (p)

def hfun (z : ↥K.fixingSubgroup × ↥K.fixingSubgroup → A p K L) : ↥K.fixingSubgroup → A p K L := fun g =>
  Finsupp.equivFunOnFinite.symm fun q =>
    z (τ.σ q, (τ.lam ((τ.σ q)⁻¹ * g) : ↥K.fixingSubgroup)) q - z (g, τ.σ ((g : ↥K.fixingSubgroup ⧸ Λ K L)⁻¹ * q)) q

lemma hfun_apply (z : ↥K.fixingSubgroup × ↥K.fixingSubgroup → A p K L) (g : ↥K.fixingSubgroup) (q : ↥K.fixingSubgroup ⧸ Λ K L) :
    hfun p K L τ z g q =
      z (τ.σ q, (τ.lam ((τ.σ q)⁻¹ * g) : ↥K.fixingSubgroup)) q - z (g, τ.σ ((g : ↥K.fixingSubgroup ⧸ Λ K L)⁻¹ * q)) q := by
  simp [hfun]

lemma ψfun_shF_sub {z : ↥K.fixingSubgroup × ↥K.fixingSubgroup → A p K L} (hz : z ∈ cocycles₂ (A p K L)) :
    ψfun p K L τ (shF p K L hKL z) - z = (d₁₂ (A p K L)).hom (hfun p K L τ z) := by
  rw [mem_cocycles₂_iff] at hz
  funext gg
  obtain ⟨g₁, g₂⟩ := gg
  apply Finsupp.ext
  intro q
  rw [Pi.sub_apply, Finsupp.sub_apply, ψfun_apply, shF_apply, d₁₂_hom_apply, Finsupp.add_apply, Finsupp.sub_apply,
    A_ρ_apply_apply', hfun_apply, hfun_apply, hfun_apply]

  set q' : ↥K.fixingSubgroup ⧸ Λ K L := (g₁ : ↥K.fixingSubgroup ⧸ Λ K L)⁻¹ * q with hq'
  have hq'' : ((g₁ * g₂ : ↥K.fixingSubgroup) : ↥K.fixingSubgroup ⧸ Λ K L)⁻¹ * q = (g₂ : ↥K.fixingSubgroup ⧸ Λ K L)⁻¹ * q' := by
    rw [QuotientGroup.mk_mul, mul_inv_rev, mul_assoc, ← hq']
  rw [hq'']
  set q'' : ↥K.fixingSubgroup ⧸ Λ K L := (g₂ : ↥K.fixingSubgroup ⧸ Λ K L)⁻¹ * q' with hq''def
  set x : ↥K.fixingSubgroup := (τ.σ q)⁻¹ with hx
  set x' : ↥K.fixingSubgroup := (τ.σ q')⁻¹ with hx'
  have hσ : (τ.σ (Transversal.qinv (x * g₁)))⁻¹ = x' := by rw [hx, qinv_σ_inv_mul, ← hq']

  have hab : lamH K L τ (x * g₁ * g₂) = lamH K L τ (x * g₁) * lamH K L τ (x' * g₂) := by
    rw [lamH_mul K L τ (x * g₁) g₂, hσ]
  have hAB : (τ.lam (x * g₁ * g₂) : ↥K.fixingSubgroup) = τ.lam (x * g₁) * τ.lam (x' * g₂) := by
    have := congrArg (incl K L hKL) hab
    rwa [map_mul, incl_lamH, incl_lamH, incl_lamH] at this
  have rel1 : g₁ * τ.σ q' = τ.σ q * (τ.lam (x * g₁) : ↥K.fixingSubgroup) := by rw [hq', hx]; exact g_mul_σ K L τ q g₁
  have rel2 : g₂ * τ.σ q'' = τ.σ q' * (τ.lam (x' * g₂) : ↥K.fixingSubgroup) := by rw [hq''def, hx']; exact g_mul_σ K L τ q' g₂
  have hcoord : ((τ.σ q : ↥K.fixingSubgroup) : ↥K.fixingSubgroup ⧸ Λ K L)⁻¹ * q = 1 := by rw [τ.mk_σ, inv_mul_cancel]

  have I1 := congrArg (fun f : ↥K.fixingSubgroup ⧸ Λ K L →₀ ZMod p => f q) (hz g₁ g₂ (τ.σ q''))
  have I2 := congrArg (fun f : ↥K.fixingSubgroup ⧸ Λ K L →₀ ZMod p => f q) (hz g₁ (τ.σ q') (τ.lam (x' * g₂) : ↥K.fixingSubgroup))
  have I3 := congrArg (fun f : ↥K.fixingSubgroup ⧸ Λ K L →₀ ZMod p => f q)
    (hz (τ.σ q) (τ.lam (x * g₁) : ↥K.fixingSubgroup) (τ.lam (x' * g₂) : ↥K.fixingSubgroup))
  simp only [Finsupp.add_apply, A_ρ_apply_apply'] at I1 I2 I3
  rw [← hq', rel1] at I2
  rw [← hq', rel2] at I1
  rw [hcoord] at I3

  rw [show x * (g₁ * g₂) = x * g₁ * g₂ from (mul_assoc _ _ _).symm, hab, inv_mul_cancel_left, incl_lamH, incl_lamH]
  dsimp only
  rw [hAB]
  linear_combination I2 - I1 - I3

end SH2
p2m_reactivate "P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2.Transversal P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2"
end
p2m_reactivate "P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2.Transversal P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2"

noncomputable section
namespace SH2

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L)
variable [(Λ K L).Normal] [(Λ K L).FiniteIndex] (τ : Transversal (Λ K L))
variable (p)

lemma ψ₁_isLevelConstantSr₁ (hL : L.IsUnramifiedOutside S) {y : ↥L.fixingSubgroup → ZMod p}
    (hy : IsLevelConstantSr₁ L.fixingSubgroup.subtype S y) :
    IsLevelConstantSr₁ K.fixingSubgroup.subtype S (ψ₁ p K L τ y) := by
  obtain ⟨F, hF, hyF⟩ := hy
  obtain ⟨N, hN, hNF, hNL, hconj⟩ := exists_deep_level hF hL
  refine ⟨N, hN, fun g u hu => ?_⟩
  change ((u : ↥K.fixingSubgroup) : Γ) ∈ N.fixingSubgroup at hu
  apply Finsupp.ext
  intro q
  rw [ψ₁_apply, ψ₁_apply]
  congr 1
  set x : ↥K.fixingSubgroup := (τ.σ q)⁻¹
  set c : ↥K.fixingSubgroup := τ.σ (Transversal.qinv (x * g))
  have huΛ : u ∈ Λ K L := Subgroup.mem_subgroupOf.2 (hNL hu)
  have huu : ((c⁻¹ * u * c : ↥K.fixingSubgroup) : Γ) ∈ N.fixingSubgroup := hconj _ hu _
  have h1 : lamH K L τ (x * (g * u)) = lamH K L τ (x * g) * toH K L (c⁻¹ * u * c) (Subgroup.mem_subgroupOf.2 (hNL huu)) := by
    apply Subtype.ext
    change ((τ.lam (x * (g * u)) : ↥K.fixingSubgroup) : Γ) = ((τ.lam (x * g) : ↥K.fixingSubgroup) : Γ) * ((c⁻¹ * u * c : ↥K.fixingSubgroup) : Γ)
    rw [← mul_assoc, τ.coe_lam_mul_of_mem (x * g) u huΛ]
    rfl
  rw [h1]
  exact hyF _ _ (hNF huu)

lemma hfun_isLevelConstantSr₁ (hL : L.IsUnramifiedOutside S) {z : ↥K.fixingSubgroup × ↥K.fixingSubgroup → A p K L}
    (hz : z ∈ levelCocyclesSr₂ K.fixingSubgroup.subtype S (A p K L)) :
    IsLevelConstantSr₁ K.fixingSubgroup.subtype S (hfun p K L τ z) := by
  obtain ⟨-, F, hF, hzF⟩ := hz
  obtain ⟨N, hN, hNF, hNL, hconj⟩ := exists_deep_level hF hL
  refine ⟨N, hN, fun g u hu => ?_⟩
  change ((u : ↥K.fixingSubgroup) : Γ) ∈ N.fixingSubgroup at hu
  apply Finsupp.ext
  intro q
  rw [hfun_apply, hfun_apply]
  have huΛ : u ∈ Λ K L := Subgroup.mem_subgroupOf.2 (hNL hu)
  have hū : ((g * u : ↥K.fixingSubgroup) : ↥K.fixingSubgroup ⧸ Λ K L) = (g : ↥K.fixingSubgroup ⧸ Λ K L) := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff u).2 huΛ, mul_one]
  rw [hū]
  congr 1
  ·
    set x : ↥K.fixingSubgroup := (τ.σ q)⁻¹
    set c : ↥K.fixingSubgroup := τ.σ (Transversal.qinv (x * g))
    have huu : ((c⁻¹ * u * c : ↥K.fixingSubgroup) : Γ) ∈ N.fixingSubgroup := hconj _ hu _
    have h1 : (τ.lam (x * (g * u)) : ↥K.fixingSubgroup) = τ.lam (x * g) * (c⁻¹ * u * c) := by
      rw [← mul_assoc, τ.coe_lam_mul_of_mem (x * g) u huΛ]
    rw [h1]
    have := hzF (τ.σ q) (τ.lam (x * g) : ↥K.fixingSubgroup) 1 (c⁻¹ * u * c) F.fixingSubgroup.one_mem (hNF huu)
    rw [mul_one] at this
    rw [this]
  ·
    have := hzF g (τ.σ ((g : ↥K.fixingSubgroup ⧸ Λ K L)⁻¹ * q)) u 1 (hNF hu) F.fixingSubgroup.one_mem
    rw [mul_one] at this
    rw [this]

end SH2
p2m_reactivate "P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2.Transversal P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2"
end
p2m_reactivate "P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2.Transversal P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2"

noncomputable section
namespace SH2

open CategoryTheory groupCohomology ExtCitation

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L)
variable [(Λ K L).Normal] [(Λ K L).FiniteIndex] (τ : Transversal (Λ K L))

include τ in
theorem sh_injective (hL : L.IsUnramifiedOutside S) : Function.Injective (sh p S K L hKL) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨z, rfl⟩ := continuousH2Srπ_surjective _ S _ a
  rw [continuousH2SrMap_continuousH2Srπ, continuousH2Srπ_eq_zero_iff, coe_levelCocyclesSr₂Map] at ha
  obtain ⟨y, hy, hyd⟩ := (mem_levelCoboundariesSr₂_iff _ S _ _).1 ha
  rw [continuousH2Srπ_eq_zero_iff]
  have hlev : ψ₁ p K L τ y - hfun p K L τ z.1 ∈ levelCochainsSr₁ K.fixingSubgroup.subtype S (A p K L) :=
    Submodule.sub_mem _ (show ψ₁ p K L τ y ∈ levelCochainsSr₁ K.fixingSubgroup.subtype S (A p K L) from
        ψ₁_isLevelConstantSr₁ p S K L τ hL hy)
      (show hfun p K L τ z.1 ∈ levelCochainsSr₁ K.fixingSubgroup.subtype S (A p K L) from
        hfun_isLevelConstantSr₁ p S K L τ hL z.2)
  refine (mem_levelCoboundariesSr₂_iff _ S _ _).2 ⟨ψ₁ p K L τ y - hfun p K L τ z.1, hlev, ?_⟩
  rw [map_sub, ← ψfun_d₁₂, hyd, ← ψfun_shF_sub p K L hKL τ z.2.1]
  abel

end SH2
p2m_reactivate "P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2.Transversal P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2"
end
p2m_reactivate "P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2.Transversal P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq.SH2"

set_option maxHeartbeats 6400000 in
open SH2 in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L) (hL : L.IsUnramifiedOutside S)
    [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal] [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).FiniteIndex] :
    ∃ Θ : continuousH2Sr K.fixingSubgroup.subtype S (cyclotomicQuotientRep K L p) ≃ₗ[ZMod p]
        continuousH2Sr L.fixingSubgroup.subtype S
          ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)),
      ∀ (z : ↥(levelCocyclesSr₂ K.fixingSubgroup.subtype S (cyclotomicQuotientRep K L p)))
          (w : ↥(levelCocyclesSr₂ L.fixingSubgroup.subtype S
            ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)))),
        (∀ s t : ↥L.fixingSubgroup,
            (w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) (s, t) =
              ((z : ↥K.fixingSubgroup × ↥K.fixingSubgroup → (↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup) →₀ ZMod p)
                (⟨(s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), IntermediateField.fixingSubgroup_antitone hKL s.2⟩,
                 ⟨(t : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), IntermediateField.fixingSubgroup_antitone hKL t.2⟩))
                (1 : ↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup)) →
          Θ (continuousH2Srπ K.fixingSubgroup.subtype S _ z) = continuousH2Srπ L.fixingSubgroup.subtype S _ w := by
  obtain ⟨τ⟩ := SH2.Transversal.nonempty (Λ := SH2.Λ K L)
  refine ⟨LinearEquiv.ofBijective (SH2.sh p S K L hKL) ⟨SH2.sh_injective S K L hKL τ hL, SH2.sh_surjective p S K L hKL τ hL⟩,
    fun z w hw => ?_⟩
  rw [LinearEquiv.ofBijective_apply, continuousH2SrMap_continuousH2Srπ]
  congr 1
  apply Subtype.ext
  funext st
  obtain ⟨s, t⟩ := st
  rw [coe_levelCocyclesSr₂Map, cochainsPullPush₂_apply]
  exact (hw s t).symm

end S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq
end P2MW
export P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_apply_eq (solution)
