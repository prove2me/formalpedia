-- Prove2me | solution 1 for groupCohomology.natCard_continuousClasses_ofChar_eq_natCard_units_quot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/62641ea4-e89f-5b0d-9606-c0106d6a56e0

import Mathlib
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_GroupCohomology_Kummer
import Theorems.Thm_IsPrimitiveRoot_existsUnique_eq_pow_val
import Theorems.Thm_groupCohomology_isMulCocycle1_pow_val_iff_mem_cocycles1_ofChar
import Theorems.Thm_groupCohomology_mem_coboundaries1_ofChar_iff_exists_rootOfUnity
import Theorems.Thm_groupCohomology_Kummer_exists_pow_eq_iff_exists_rootOfUnity_coboundary
import Theorems.Thm_groupCohomology_Kummer_kummerCocycle_mul_eq_of_mem_fixingSubgroup_adjoin
import Theorems.Thm_groupCohomology_Kummer_exists_kummerCocycle_eq_of_isMulCocycle1_of_level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_natCard_continuousClasses_ofChar_eq_natCard_units_quot

set_option autoImplicit false
universe u
open CategoryTheory groupCohomology
open groupCohomology.Kummer
open scoped IntermediateField Pointwise

theorem solution
    {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L] {p : ℕ} [Fact p.Prime]
    (χ : (L ≃ₐ[K] L) →* (ZMod p)ˣ) {ζ : Lˣ} (hζp : IsPrimitiveRoot ζ p)
    (hζ : ∀ g : L ≃ₐ[K] L, g • ζ = ζ ^ (χ g : ZMod p).val)
    (hroots : ∀ a : Kˣ, ∃ α : Lˣ, algebraMap K L (a : K) = (α : L) ^ p)
    (adm : Submodule (ZMod p) (H1 (ofChar χ)))
    (hadm : ∀ x, x ∈ adm ↔ ∃ c : cocycles₁ (ofChar χ),
      (∃ E : IntermediateField K L, FiniteDimensional K E ∧
        ∀ g s : L ≃ₐ[K] L, s ∈ E.fixingSubgroup → c.val (g * s) = c.val g) ∧ (H1π _).hom c = x) :
    Nat.card adm = Nat.card (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) := by
  classical
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : NeZero p := ⟨hp0⟩

  have hinj : ∀ a b : ZMod p, ζ ^ a.val = ζ ^ b.val → a = b := fun a b h =>
    ZMod.val_injective p (hζp.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h)
  have hpowadd : ∀ a b : ZMod p, ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
    intro a b
    rw [← pow_add, pow_eq_pow_iff_modEq, ← hζp.eq_orderOf, ← ZMod.natCast_eq_natCast_iff]
    simp only [ZMod.natCast_zmod_val, Nat.cast_add]

  have hδex : ∀ f : (L ≃ₐ[K] L) → Lˣ, (∀ g, f g ^ p = 1) →
      ∃ c : (L ≃ₐ[K] L) → ZMod p, ∀ g, f g = ζ ^ (c g).val := fun f hf =>
    (hζp.existsUnique_eq_pow_val f hf).exists
  choose δ hδ using hδex
  have hδuniq : ∀ f hf (c : (L ≃ₐ[K] L) → ZMod p), (∀ g, f g = ζ ^ (c g).val) → c = δ f hf :=
    fun f hf c hc => funext fun g => hinj _ _ ((hc g).symm.trans (hδ f hf g))

  have hκp : ∀ (a : Kˣ) (α : Lˣ), algebraMap K L (a : K) = (α : L) ^ p → ∀ g, kummerCocycle (K := K) α g ^ p = 1 :=
    fun a α hα g => kummerCocycle_pow_eq_one hα g
  have hκcoc : ∀ (a : Kˣ) (α : Lˣ) (hα : algebraMap K L (a : K) = (α : L) ^ p),
      δ (kummerCocycle α) (hκp a α hα) ∈ cocycles₁ (ofChar χ) := by
    intro a α hα
    rw [← isMulCocycle1_pow_val_iff_mem_cocycles1_ofChar χ hζp hζ]
    have : (fun g => ζ ^ (δ (kummerCocycle α) (hκp a α hα) g).val) = kummerCocycle (K := K) α :=
      funext fun g => (hδ _ _ g).symm
    rw [this]
    exact isMulCocycle₁_kummerCocycle α

  let z : ∀ (a : Kˣ) (α : Lˣ), algebraMap K L (a : K) = (α : L) ^ p → H1 (ofChar χ) :=
    fun a α hα => (H1π (ofChar χ)).hom ⟨δ (kummerCocycle α) (hκp a α hα), hκcoc a α hα⟩

  have hz_mul : ∀ (a : Kˣ) (α : Lˣ) (hα : algebraMap K L (a : K) = (α : L) ^ p)
      (b : Kˣ) (β : Lˣ) (hβ : algebraMap K L (b : K) = (β : L) ^ p)
      (c : Kˣ) (γ : Lˣ) (hγ : algebraMap K L (c : K) = (γ : L) ^ p),
      c = a * b → γ = α * β → z c γ hγ = z a α hα + z b β hβ := by
    rintro a α hα b β hβ c γ hγ rfl rfl
    simp only [z, ← map_add]
    congr 1
    apply Subtype.ext
    show δ (kummerCocycle (α * β)) _ = δ (kummerCocycle α) _ + δ (kummerCocycle β) _
    symm
    apply hδuniq
    intro g
    rw [kummerCocycle_mul, Pi.add_apply, hpowadd, ← hδ, ← hδ]

  have hz_zero : ∀ (a : Kˣ) (α : Lˣ) (hα : algebraMap K L (a : K) = (α : L) ^ p),
      z a α hα = 0 ↔ ∃ b : Kˣ, b ^ p = a := by
    intro a α hα
    simp only [z]
    rw [H1π_eq_zero_iff, exists_pow_eq_iff_exists_rootOfUnity_coboundary hα]
    show δ (kummerCocycle α) (hκp a α hα) ∈ coboundaries₁ (ofChar χ) ↔ _
    rw [mem_coboundaries1_ofChar_iff_exists_rootOfUnity χ hζp hζ]
    refine exists_congr fun η => and_congr_right fun _ => forall_congr' fun g => ?_
    rw [← hδ]

  have hz_mem : ∀ (a : Kˣ) (α : Lˣ) (hα : algebraMap K L (a : K) = (α : L) ^ p), z a α hα ∈ adm := by
    intro a α hα
    rw [hadm]
    refine ⟨⟨δ (kummerCocycle α) (hκp a α hα), hκcoc a α hα⟩, ?_, rfl⟩
    haveI : FiniteDimensional K K⟮(α : L)⟯ :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (α : L))
    refine ⟨K⟮(α : L)⟯, inferInstance, fun g s hs => hinj _ _ ?_⟩
    show ζ ^ (δ (kummerCocycle α) _ (g * s)).val = ζ ^ (δ (kummerCocycle α) _ g).val
    rw [← hδ, ← hδ]
    exact kummerCocycle_mul_eq_of_mem_fixingSubgroup_adjoin α g s hs

  have hz_surj : ∀ x ∈ adm, ∃ (a : Kˣ) (α : Lˣ) (hα : algebraMap K L (a : K) = (α : L) ^ p),
      z a α hα = x := by
    intro x hx
    obtain ⟨c, ⟨E, hE, hlev⟩, rfl⟩ := (hadm x).mp hx
    let f : (L ≃ₐ[K] L) → Lˣ := fun g => ζ ^ (c.val g).val
    have hf : IsMulCocycle₁ f := (isMulCocycle1_pow_val_iff_mem_cocycles1_ofChar χ hζp hζ c.val).mpr c.2
    have hfp : ∀ g, f g ^ p = 1 := fun g => by
      simp only [f]
      rw [← pow_mul, mul_comm, pow_mul, hζp.pow_eq_one, one_pow]
    have hflc : ∃ E : IntermediateField K L, FiniteDimensional K E ∧
        ∀ σ τ : L ≃ₐ[K] L, τ ∈ E.fixingSubgroup → f (σ * τ) = f σ :=
      ⟨E, hE, fun σ τ hτ => by simp only [f, hlev σ τ hτ]⟩
    obtain ⟨a, α, hα, hfκ⟩ := exists_kummerCocycle_eq_of_isMulCocycle1_of_level hf hfp hflc
    refine ⟨a, α, hα, ?_⟩
    simp only [z]
    congr 1
    apply Subtype.ext
    show δ (kummerCocycle α) _ = c.val
    symm
    apply hδuniq
    intro g
    exact (hfκ g).symm

  have hz_fib : ∀ (a : Kˣ) (α : Lˣ) (hα : algebraMap K L (a : K) = (α : L) ^ p)
      (b : Kˣ) (β : Lˣ) (hβ : algebraMap K L (b : K) = (β : L) ^ p),
      z a α hα = z b β hβ ↔ a⁻¹ * b ∈ (powMonoidHom p : Kˣ →* Kˣ).range := by
    intro a α hα b β hβ
    have hγ : algebraMap K L ((a⁻¹ * b : Kˣ) : K) = ((α⁻¹ * β : Lˣ) : L) ^ p := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mul, Units.val_inv_eq_inv_val, map_mul,
        map_inv₀, hα, hβ, mul_pow, inv_pow]
    have hsplit : z b β hβ = z a α hα + z (a⁻¹ * b) (α⁻¹ * β) hγ :=
      hz_mul a α hα (a⁻¹ * b) (α⁻¹ * β) hγ b β hβ (by rw [mul_inv_cancel_left]) (by rw [mul_inv_cancel_left])
    rw [hsplit, left_eq_add, hz_zero (a⁻¹ * b) (α⁻¹ * β) hγ, MonoidHom.mem_range]
    simp only [powMonoidHom_apply]

  choose rt hrt using hroots
  have hΦmem : ∀ a : Kˣ, z a (rt a) (hrt a) ∈ adm := fun a => hz_mem a (rt a) (hrt a)
  let Φ : Kˣ → ↥adm := fun a => Subtype.mk (z a (rt a) (hrt a)) (hΦmem a)
  have hΦ : ∀ a b : Kˣ, Φ a = Φ b ↔ a⁻¹ * b ∈ (powMonoidHom p : Kˣ →* Kˣ).range := fun a b =>
    Subtype.ext_iff.trans (hz_fib a (rt a) (hrt a) b (rt b) (hrt b))
  have hΦresp : ∀ a b : Kˣ, QuotientGroup.leftRel (powMonoidHom p : Kˣ →* Kˣ).range a b → Φ a = Φ b :=
    fun a b h => (hΦ a b).mpr (QuotientGroup.leftRel_apply.mp h)
  let Ψ : Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range → ↥adm := Quotient.lift Φ hΦresp
  have hΨ : Function.Bijective Ψ := by
    constructor
    · intro x y h
      induction x using Quotient.inductionOn with | h a => ?_
      induction y using Quotient.inductionOn with | h b => ?_
      exact Quotient.sound (QuotientGroup.leftRel_apply.mpr ((hΦ a b).mp h))
    · rintro ⟨x, hx⟩
      obtain ⟨a, α, hα, hzx⟩ := hz_surj x hx
      refine ⟨Quotient.mk _ a, Subtype.ext ?_⟩
      show z a (rt a) (hrt a) = x
      rw [← hzx, hz_fib a (rt a) (hrt a) a α hα, inv_mul_cancel]
      exact one_mem _
  exact (Nat.card_congr (Equiv.ofBijective Ψ hΨ)).symm

end S_groupCohomology_natCard_continuousClasses_ofChar_eq_natCard_units_quot
end P2MW
export P2MW.S_groupCohomology_natCard_continuousClasses_ofChar_eq_natCard_units_quot (solution)
