-- Prove2me | solution 1 for northcott_projMulHeight_numberField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/dda51262-f887-5d31-9d1e-b904574cee57

import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Northcott
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_northcott_projMulHeight_numberField

set_option autoImplicit false

noncomputable section

open Height NumberField IsDedekindDomain Function

namespace NorthcottPort

section DenominatorIdeal

variable (F : Type*) [Field F] [NumberField F]

def denIdeal (x : F) : Ideal (𝓞 F) :=
  Submodule.comap (LinearMap.toSpanSingleton (𝓞 F) F x)
    (LinearMap.range (Algebra.linearMap (𝓞 F) F))

variable {F}

omit [NumberField F] in

theorem mem_denIdeal_iff {x : F} {a : 𝓞 F} :
    a ∈ denIdeal F x ↔ ∃ n : 𝓞 F, algebraMap (𝓞 F) F n = algebraMap (𝓞 F) F a * x := by
  simp only [denIdeal, Submodule.mem_comap, LinearMap.mem_range,
    LinearMap.toSpanSingleton_apply, Algebra.linearMap_apply, Algebra.smul_def]

omit [NumberField F] in

theorem denIdeal_eq_top_of_integral (n : 𝓞 F) :
    denIdeal F (algebraMap (𝓞 F) F n) = ⊤ := by
  rw [Ideal.eq_top_iff_one, mem_denIdeal_iff]
  exact ⟨n, by rw [map_one, one_mul]⟩

theorem denIdeal_ne_bot (x : F) : denIdeal F x ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have hbne : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨b, ?_, hbne⟩
  rw [mem_denIdeal_iff]
  refine ⟨a, ?_⟩
  have hbF : algebraMap (𝓞 F) F b ≠ 0 := by
    simpa using (map_ne_zero_iff _ (NumberField.RingOfIntegers.coe_injective (K := F))).mpr hbne
  rw [← hab, mul_div_cancel₀ _ hbF]

theorem absNorm_denIdeal_pos (x : F) : 0 < Ideal.absNorm (denIdeal F x) := by
  rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
  exact denIdeal_ne_bot x

theorem absNorm_denIdeal_clears (x : F) :
    ∃ n : 𝓞 F, ((Ideal.absNorm (denIdeal F x) : ℕ) : F) * x = algebraMap (𝓞 F) F n := by
  have hmem : ((Ideal.absNorm (denIdeal F x) : ℕ) : 𝓞 F) ∈ denIdeal F x :=
    Ideal.absNorm_mem (denIdeal F x)
  rw [mem_denIdeal_iff] at hmem
  obtain ⟨n, hn⟩ := hmem
  refine ⟨n, ?_⟩
  rw [map_natCast] at hn
  exact hn.symm

end DenominatorIdeal

section IntegralHeights

variable {F : Type*} [Field F] [NumberField F]

theorem finitePlace_algebraMap_le_one (w : FinitePlace F) (n : 𝓞 F) :
    w (algebraMap (𝓞 F) F n) ≤ 1 := by
  rw [← NumberField.FinitePlace.norm_embedding_eq w (algebraMap (𝓞 F) F n)]
  exact NumberField.FinitePlace.norm_le_one F (NumberField.FinitePlace.maximalIdeal w) n

theorem finprod_finitePlace_max_algebraMap_eq_one (n : 𝓞 F) :
    (∏ᶠ w : FinitePlace F, max (w (algebraMap (𝓞 F) F n)) 1) = 1 :=
  finprod_eq_one_of_forall_eq_one fun w =>
    max_eq_right (finitePlace_algebraMap_le_one w n)

theorem mulHeight₁_algebraMap_eq_archProd (n : 𝓞 F) :
    mulHeight₁ (algebraMap (𝓞 F) F n)
      = ∏ w : InfinitePlace F, max (w (algebraMap (𝓞 F) F n)) 1 ^ w.mult := by
  rw [NumberField.mulHeight₁_eq, finprod_finitePlace_max_algebraMap_eq_one, mul_one]

theorem infinitePlace_le_mulHeight₁_algebraMap (w : InfinitePlace F) (n : 𝓞 F) :
    w (algebraMap (𝓞 F) F n) ≤ mulHeight₁ (algebraMap (𝓞 F) F n) := by
  rw [mulHeight₁_algebraMap_eq_archProd]
  calc w (algebraMap (𝓞 F) F n)
      ≤ ∏ v : InfinitePlace F, max (v (algebraMap (𝓞 F) F n)) 1 :=
        Finset.le_prod_max_one (Finset.mem_univ w) (fun v => v (algebraMap (𝓞 F) F n))
    _ ≤ ∏ v : InfinitePlace F, max (v (algebraMap (𝓞 F) F n)) 1 ^ v.mult :=
        Finset.prod_le_prod (fun v _ => le_max_of_le_right zero_le_one)
          (fun v _ => le_self_pow₀ (le_max_right _ _) v.mult_ne_zero)

omit [NumberField F] in

theorem infinitePlace_natCast (w : InfinitePlace F) (m : ℕ) :
    w ((m : F)) = m := by
  rw [← NumberField.InfinitePlace.norm_embedding_eq w ((m : F)),
    map_natCast (NumberField.InfinitePlace.embedding w) m]
  exact RCLike.norm_natCast m

theorem mulHeight₁_natCast_eq_pow_finrank (m : ℕ) (hm : m ≠ 0) :
    mulHeight₁ ((m : F)) = (m : ℝ) ^ Module.finrank ℚ F := by
  have hcast : algebraMap (𝓞 F) F ((m : ℕ) : 𝓞 F) = ((m : ℕ) : F) :=
    map_natCast (algebraMap (𝓞 F) F) m
  have h1m : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
  rw [← hcast, mulHeight₁_algebraMap_eq_archProd]
  have hfac : ∀ w : InfinitePlace F,
      max (w (algebraMap (𝓞 F) F ((m : ℕ) : 𝓞 F))) 1 ^ w.mult = (m : ℝ) ^ w.mult := by
    intro w
    rw [hcast, infinitePlace_natCast w m, max_eq_left h1m]
  rw [Finset.prod_congr rfl fun w _ => hfac w, Finset.prod_pow_eq_pow_sum,
    NumberField.InfinitePlace.sum_mult_eq]

end IntegralHeights

section IntegralNorthcott

variable {F : Type*} [Field F] [NumberField F]

theorem finite_setOf_integral_mulHeight₁_le (B : ℝ) :
    {n : 𝓞 F | mulHeight₁ (algebraMap (𝓞 F) F n) ≤ B}.Finite := by
  have hfin : {x : F | IsIntegral ℤ x ∧ ∀ φ : F →+* ℂ, ‖φ x‖ ≤ max B 1}.Finite :=
    NumberField.Embeddings.finite_of_norm_le F ℂ (max B 1)
  have hpre : ((algebraMap (𝓞 F) F) ⁻¹'
      {x : F | IsIntegral ℤ x ∧ ∀ φ : F →+* ℂ, ‖φ x‖ ≤ max B 1}).Finite :=
    hfin.preimage (NumberField.RingOfIntegers.coe_injective (K := F)).injOn
  refine hpre.subset ?_
  intro n hn
  rw [Set.mem_setOf_eq] at hn
  refine ⟨NumberField.RingOfIntegers.isIntegral_coe n, fun φ => ?_⟩
  have h1 : ‖φ (algebraMap (𝓞 F) F n)‖
      = (NumberField.InfinitePlace.mk φ) (algebraMap (𝓞 F) F n) :=
    (NumberField.InfinitePlace.apply φ _).symm
  rw [h1]
  exact ((infinitePlace_le_mulHeight₁_algebraMap (NumberField.InfinitePlace.mk φ) n).trans
    hn).trans (le_max_left B 1)

end IntegralNorthcott

section Dictionary

theorem sup_pow_eq_pow_min {A : Type*} [CommSemiring A] (p : Ideal A) (m n : ℕ) :
    p ^ m ⊔ p ^ n = p ^ min m n := by
  rcases le_total m n with h | h
  · rw [min_eq_left h]
    exact sup_eq_left.mpr (Ideal.pow_le_pow_right h)
  · rw [min_eq_right h]
    exact sup_eq_right.mpr (Ideal.pow_le_pow_right h)

theorem max_div_pow_mul_pow_min_eq {N : ℝ} (hN : 1 < N) (m n : ℕ) :
    max (N ^ n / N ^ m) 1 * N ^ min m n = N ^ n := by
  have hN0 : (0 : ℝ) < N := one_pos.trans hN
  rcases le_total m n with h | h
  · have h1 : (1 : ℝ) ≤ N ^ n / N ^ m := by
      rw [le_div_iff₀ (pow_pos hN0 m), one_mul]
      exact pow_le_pow_right₀ hN.le h
    rw [min_eq_left h, max_eq_left h1, div_mul_cancel₀ _ (pow_pos hN0 m).ne']
  · have h1 : N ^ n / N ^ m ≤ 1 := by
      rw [div_le_one (pow_pos hN0 m)]
      exact pow_le_pow_right₀ hN.le h
    rw [min_eq_right h, max_eq_right h1, one_mul]

variable {F : Type*} [Field F] [NumberField F]

theorem max_norm_embedding_div_mul_absNorm_sup (v : HeightOneSpectrum (𝓞 F)) {a b : 𝓞 F}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    max (‖FinitePlace.embedding v (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b)‖) 1
      * (Ideal.absNorm (v.maxPowDividing (Ideal.span {a}) ⊔ v.maxPowDividing (Ideal.span {b})) : ℝ)
      = (Ideal.absNorm (v.maxPowDividing (Ideal.span {b})) : ℝ) := by
  obtain ⟨m, hm⟩ : ∃ m, v.maxPowDividing (Ideal.span {a}) = v.asIdeal ^ m := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, v.maxPowDividing (Ideal.span {b}) = v.asIdeal ^ n := ⟨_, rfl⟩
  have hN : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hN0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := one_pos.trans hN
  have hpm : ((Ideal.absNorm v.asIdeal : ℝ) ^ m) ≠ 0 := (pow_pos hN0 m).ne'
  have hpn : ((Ideal.absNorm v.asIdeal : ℝ) ^ n) ≠ 0 := (pow_pos hN0 n).ne'
  have hA := NumberField.HeightOneSpectrum.embedding_mul_absNorm F v ha
  have hB := NumberField.HeightOneSpectrum.embedding_mul_absNorm F v hb
  rw [hm, map_pow, Nat.cast_pow] at hA
  rw [hn, map_pow, Nat.cast_pow] at hB
  have ha' : ‖FinitePlace.embedding v (algebraMap (𝓞 F) F a)‖
      = ((Ideal.absNorm v.asIdeal : ℝ) ^ m)⁻¹ := by
    field_simp
    linear_combination hA
  have hb' : ‖FinitePlace.embedding v (algebraMap (𝓞 F) F b)‖
      = ((Ideal.absNorm v.asIdeal : ℝ) ^ n)⁻¹ := by
    field_simp
    linear_combination hB
  rw [hm, hn, sup_pow_eq_pow_min, map_pow, Nat.cast_pow, map_pow, Nat.cast_pow,
    map_div₀, norm_div, ha', hb', inv_div_inv]
  exact max_div_pow_mul_pow_min_eq hN m n

theorem absNorm_denIdeal_le_finprod_finitePlace_max (x : F) (hx : x ≠ 0) :
    (Ideal.absNorm (denIdeal F x) : ℝ) ≤ ∏ᶠ w : FinitePlace F, max (w x) 1 := by
  obtain ⟨a, b, hbmem, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have hb : b ≠ 0 := nonZeroDivisors.ne_zero hbmem
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hx
    exact hx rfl
  have hbF : algebraMap (𝓞 F) F b ≠ 0 :=
    (FaithfulSMul.algebraMap_eq_zero_iff (𝓞 F) F).not.mpr hb
  have hspa : Ideal.span {a} ≠ (0 : Ideal (𝓞 F)) := by
    rw [Submodule.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact ha
  have hspb : Ideal.span {b} ≠ (0 : Ideal (𝓞 F)) := by
    rw [Submodule.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact hb
  have hfa : (mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      v.maxPowDividing (Ideal.span {a})).Finite := Ideal.hasFiniteMulSupport hspa
  have hfb : (mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      v.maxPowDividing (Ideal.span {b})).Finite := Ideal.hasFiniteMulSupport hspb
  set T : Finset (HeightOneSpectrum (𝓞 F)) := (hfa.union hfb).toFinset with hTdef
  have hmemT : ∀ v : HeightOneSpectrum (𝓞 F),
      v ∈ (mulSupport fun v : HeightOneSpectrum (𝓞 F) => v.maxPowDividing (Ideal.span {a})) ∪
        (mulSupport fun v : HeightOneSpectrum (𝓞 F) => v.maxPowDividing (Ideal.span {b})) →
        v ∈ T := by
    intro v hv
    rw [hTdef, Set.Finite.mem_toFinset]
    exact hv
  have hsub_a : (mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      v.maxPowDividing (Ideal.span {a})) ⊆ ↑T := fun v hv =>
    Finset.mem_coe.mpr (hmemT v (Set.mem_union_left _ hv))
  have hsub_b : (mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      v.maxPowDividing (Ideal.span {b})) ⊆ ↑T := fun v hv =>
    Finset.mem_coe.mpr (hmemT v (Set.mem_union_right _ hv))
  have hTa : (∏ v ∈ T, v.maxPowDividing (Ideal.span {a})) = Ideal.span {a} := by
    rw [← finprod_eq_prod_of_mulSupport_subset _ hsub_a,
      Ideal.finprod_heightOneSpectrum_factorization hspa]
  have hTb : (∏ v ∈ T, v.maxPowDividing (Ideal.span {b})) = Ideal.span {b} := by
    rw [← finprod_eq_prod_of_mulSupport_subset _ hsub_b,
      Ideal.finprod_heightOneSpectrum_factorization hspb]
  set Imin : Ideal (𝓞 F) :=
    ∏ v ∈ T, (v.maxPowDividing (Ideal.span {a}) ⊔ v.maxPowDividing (Ideal.span {b}))
    with hImindef
  have hdvd_a : Imin ∣ Ideal.span {a} := by
    rw [← hTa, hImindef]
    exact Finset.prod_dvd_prod_of_dvd _ _ fun v _ => Ideal.dvd_iff_le.mpr le_sup_left
  have hdvd_b : Imin ∣ Ideal.span {b} := by
    rw [← hTb, hImindef]
    exact Finset.prod_dvd_prod_of_dvd _ _ fun v _ => Ideal.dvd_iff_le.mpr le_sup_right
  have hImin0 : Imin ≠ 0 := by
    intro h0
    obtain ⟨D, hD⟩ := hdvd_a
    rw [h0, zero_mul] at hD
    exact hspa hD
  obtain ⟨C, hC⟩ := hdvd_b
  have hC0 : C ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hC
    exact hspb hC
  have hCden : C ≤ denIdeal F (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) := by
    intro c hc
    rw [mem_denIdeal_iff]
    have hmem : a * c ∈ Ideal.span {a} * C :=
      Ideal.mul_mem_mul (Ideal.mem_span_singleton_self a) hc
    have hle : Ideal.span {a} * C ≤ Ideal.span {b} := by
      rw [hC]
      exact Ideal.mul_mono_left (Ideal.le_of_dvd hdvd_a)
    obtain ⟨n, hn⟩ := Ideal.mem_span_singleton'.mp (hle hmem)
    refine ⟨n, ?_⟩
    have hcast := congrArg (algebraMap (𝓞 F) F) hn
    rw [map_mul, map_mul] at hcast
    rw [← mul_div_assoc, eq_div_iff hbF]
    linear_combination hcast
  have hNC_pos : 0 < Ideal.absNorm C := by
    rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, ← Submodule.zero_eq_bot]
    exact hC0
  have hNden_le : Ideal.absNorm (denIdeal F (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b))
      ≤ Ideal.absNorm C :=
    Nat.le_of_dvd hNC_pos (Ideal.absNorm_dvd_absNorm_of_le hCden)
  have hsub_x : (mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      max (‖FinitePlace.embedding v (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b)‖) 1) ⊆ ↑T := by
    intro v hv
    rw [Function.mem_mulSupport] at hv
    have h1 : 1 < ‖FinitePlace.embedding v (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b)‖ := by
      rcases le_or_gt (‖FinitePlace.embedding v
          (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b)‖) 1 with hle | hgt
      · exact absurd (max_eq_right hle) hv
      · exact hgt
    rw [map_div₀, norm_div] at h1
    have hbpos : 0 < ‖FinitePlace.embedding v (algebraMap (𝓞 F) F b)‖ := by
      rcases (norm_nonneg (FinitePlace.embedding v (algebraMap (𝓞 F) F b))).lt_or_eq
        with hpos | heq
      · exact hpos
      · exfalso
        have hB := NumberField.HeightOneSpectrum.embedding_mul_absNorm F v hb
        rw [← heq, zero_mul] at hB
        exact zero_ne_one hB
    have hblt : ‖FinitePlace.embedding v (algebraMap (𝓞 F) F b)‖ < 1 := by
      have h2 : ‖FinitePlace.embedding v (algebraMap (𝓞 F) F b)‖ <
          ‖FinitePlace.embedding v (algebraMap (𝓞 F) F a)‖ := by
        rwa [lt_div_iff₀ hbpos, one_mul] at h1
      exact h2.trans_le (NumberField.FinitePlace.norm_le_one F v a)
    have hmaxb : v ∈ mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
        v.maxPowDividing (Ideal.span {b}) := by
      rw [Function.mem_mulSupport]
      intro heq
      have hB := NumberField.HeightOneSpectrum.embedding_mul_absNorm F v hb
      rw [heq, map_one, Nat.cast_one, mul_one] at hB
      rw [hB] at hblt
      exact lt_irrefl 1 hblt
    exact Finset.mem_coe.mpr (hmemT v (Set.mem_union_right _ hmaxb))
  have hfp : (∏ᶠ w : FinitePlace F, max (w (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b)) 1)
      = ∏ v ∈ T, max (‖FinitePlace.embedding v
          (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b)‖) 1 := by
    rw [← finprod_comp_equiv NumberField.FinitePlace.equivHeightOneSpectrum.symm]
    simp only [NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply]
    exact finprod_eq_prod_of_mulSupport_subset _ hsub_x
  have hdict : (∏ v ∈ T, max (‖FinitePlace.embedding v
        (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b)‖) 1) * (Ideal.absNorm Imin : ℝ)
      = (Ideal.absNorm (Ideal.span {b}) : ℝ) := by
    have h1 : (Ideal.absNorm Imin : ℝ)
        = ∏ v ∈ T, (Ideal.absNorm (v.maxPowDividing (Ideal.span {a}) ⊔
            v.maxPowDividing (Ideal.span {b})) : ℝ) := by
      rw [hImindef, map_prod, Nat.cast_prod]
    have h2 : (Ideal.absNorm (Ideal.span {b}) : ℝ)
        = ∏ v ∈ T, (Ideal.absNorm (v.maxPowDividing (Ideal.span {b})) : ℝ) := by
      conv_lhs => rw [← hTb]
      rw [map_prod, Nat.cast_prod]
    rw [h1, h2, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => max_norm_embedding_div_mul_absNorm_sup v ha hb
  have hImin_pos : (0 : ℝ) < (Ideal.absNorm Imin : ℝ) := by
    rw [Nat.cast_pos, Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, ← Submodule.zero_eq_bot]
    exact hImin0
  have hNb_split : (Ideal.absNorm (Ideal.span {b}) : ℝ)
      = (Ideal.absNorm Imin : ℝ) * (Ideal.absNorm C : ℝ) := by
    rw [hC, map_mul, Nat.cast_mul]
  have hfpC : (∏ᶠ w : FinitePlace F, max (w (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b)) 1)
      = (Ideal.absNorm C : ℝ) := by
    have heq := hdict
    rw [hNb_split] at heq
    rw [hfp]
    exact mul_right_cancel₀ hImin_pos.ne' (heq.trans (mul_comm _ _))
  rw [hfpC]
  exact_mod_cast hNden_le

theorem denominatorNormBound (x : F) (hx : x ≠ 0) :
    (Ideal.absNorm (denIdeal F x) : ℝ) ≤ mulHeight₁ x := by
  rw [NumberField.mulHeight₁_eq]
  refine (absNorm_denIdeal_le_finprod_finitePlace_max x hx).trans ?_
  refine le_mul_of_one_le_left (finprod_nonneg fun w => ?_) (Finset.one_le_prod fun w _ => ?_)
  · exact zero_le_one.trans (le_max_right _ _)
  · exact one_le_pow₀ (le_max_right _ _)

theorem denominatorClearingBound (x : F) (hx : x ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ mulHeight₁ x ∧
      ∃ n : 𝓞 F, ((m : ℕ) : F) * x = algebraMap (𝓞 F) F n :=
  ⟨Ideal.absNorm (denIdeal F x), absNorm_denIdeal_pos x, denominatorNormBound x hx,
    absNorm_denIdeal_clears x⟩

end Dictionary

section CoveringEngine

variable {F : Type*} [Field F] [NumberField F]

theorem finite_setOf_mulHeight₁_le (B : ℝ) :
    {x : F | mulHeight₁ x ≤ B}.Finite := by
  set B' : ℝ := max B 1 with hB'def
  have hB'1 : (1 : ℝ) ≤ B' := le_max_right B 1
  set d : ℕ := Module.finrank ℚ F with hd_def
  refine Set.Finite.subset (Set.Finite.insert 0
    (Set.Finite.biUnion (Set.finite_Icc 1 ⌈B'⌉₊) (fun m _ =>
      (finite_setOf_integral_mulHeight₁_le (B' ^ d * B')).image
        (fun n : 𝓞 F => algebraMap (𝓞 F) F n / ((m : ℕ) : F))))) ?_
  intro x hx
  rw [Set.mem_setOf_eq] at hx
  have hxB' : mulHeight₁ x ≤ B' := hx.trans (le_max_left B 1)
  rcases eq_or_ne x 0 with rfl | hx0
  · exact Set.mem_insert 0 _
  refine Set.mem_insert_of_mem 0 ?_
  obtain ⟨m, hm0, hmle, n, hn⟩ := denominatorClearingBound x hx0
  have hmleB' : (m : ℝ) ≤ B' := hmle.trans hxB'
  rw [Set.mem_iUnion₂]
  refine ⟨m, ?_, ?_⟩
  · rw [Set.mem_Icc]
    refine ⟨hm0, ?_⟩
    have h1 : (m : ℝ) ≤ (⌈B'⌉₊ : ℝ) := hmleB'.trans (Nat.le_ceil B')
    exact_mod_cast h1
  · rw [Set.mem_image]
    refine ⟨n, ?_, ?_⟩
    · rw [Set.mem_setOf_eq, ← hn]
      have hnat := mulHeight₁_natCast_eq_pow_finrank (F := F) m hm0.ne'
      calc mulHeight₁ (((m : ℕ) : F) * x)
          ≤ mulHeight₁ (((m : ℕ) : F)) * mulHeight₁ x := mulHeight₁_mul_le _ _
        _ = (m : ℝ) ^ d * mulHeight₁ x := by rw [hnat]
        _ ≤ B' ^ d * B' := by
            have hmd : (m : ℝ) ^ d ≤ B' ^ d := by gcongr
            exact mul_le_mul hmd hxB' (mulHeight₁_nonneg x) (by positivity)
    · have hmF : ((m : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr hm0.ne'
      rw [div_eq_iff hmF, ← hn]
      ring

scoped instance instNorthcottMulHeightNumberField (F : Type*) [Field F] [NumberField F] :
    Northcott (mulHeight₁ : F → ℝ) :=
  ⟨finite_setOf_mulHeight₁_le⟩

end CoveringEngine

end NorthcottPort
p2m_reactivate "P2MW.S_northcott_projMulHeight_numberField.NorthcottPort"

namespace Projectivization
p2m_export "Projectivization" "mk_rep mulHeight_mk mk mulHeight rep_nonzero smul_def map logHeight_eq_log_mulHeight mulHeight_pos logHeight mk_eq_mk_iff'"
p2m_open "Projectivization"

open Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι : Type*} [Finite ι]

lemma mulHeight₁_div_le_mulHeight (x : ι → K) (i j : ι) :
    mulHeight₁ (x i / x j) ≤ Height.mulHeight x := by
  rw [mulHeight₁_div_eq_mulHeight]
  have h : ![x i, x j] = x ∘ ![i, j] := by
    ext k
    fin_cases k <;> simp
  rw [h]
  exact Height.mulHeight_comp_le ![i, j] x

noncomputable def affineCoords (j : ι) (P : Projectivization K (ι → K)) : ι → K :=
  fun i => P.rep i / P.rep j

omit [AdmissibleAbsValues K] [Finite ι] in
@[scoped simp]
lemma affineCoords_apply (j : ι) (P : Projectivization K (ι → K)) (i : ι) :
    affineCoords j P i = P.rep i / P.rep j :=
  rfl

lemma mulHeight₁_affineCoords_le (j : ι) (P : Projectivization K (ι → K)) (i : ι) :
    mulHeight₁ (affineCoords j P i) ≤ mulHeight P := by
  conv_rhs => rw [← P.mk_rep, mulHeight_mk]
  exact mulHeight₁_div_le_mulHeight P.rep i j

omit [AdmissibleAbsValues K] [Finite ι] in

lemma affineCoords_injOn (j : ι) :
    Set.InjOn (affineCoords j) {P : Projectivization K (ι → K) | P.rep j ≠ 0} := by
  intro P hP Q hQ h
  rw [Set.mem_setOf_eq] at hP hQ
  rw [← P.mk_rep, ← Q.mk_rep, mk_eq_mk_iff']
  refine ⟨P.rep j / Q.rep j, ?_⟩
  ext i
  have hi : P.rep i / P.rep j = Q.rep i / Q.rep j := congrFun h i
  rw [div_eq_div_iff hP hQ] at hi
  rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_comm, eq_div_iff hQ]
  linear_combination hi

lemma finite_setOf_mulHeight_le_inter_chart [Northcott (mulHeight₁ : K → ℝ)] (j : ι) (b : ℝ) :
    {P : Projectivization K (ι → K) | mulHeight P ≤ b ∧ P.rep j ≠ 0}.Finite := by
  have hfin : {f : ι → K | ∀ i, f i ∈ {q : K | mulHeight₁ q ≤ b}}.Finite :=
    Set.Finite.pi' fun _ => Northcott.finite_le b
  refine Set.Finite.of_finite_image (hfin.subset ?_) ((affineCoords_injOn j).mono fun P hP => hP.2)
  rintro _ ⟨P, ⟨hPb, _⟩, rfl⟩ i
  exact (mulHeight₁_affineCoords_le j P i).trans hPb

theorem finite_setOf_mulHeight_le [Northcott (mulHeight₁ : K → ℝ)] (b : ℝ) :
    {P : Projectivization K (ι → K) | mulHeight P ≤ b}.Finite := by
  refine (Set.finite_iUnion fun j : ι => finite_setOf_mulHeight_le_inter_chart j b).subset
    fun P hP => ?_
  obtain ⟨j, hj⟩ := Function.ne_iff.mp P.rep_nonzero
  exact Set.mem_iUnion.mpr ⟨j, hP, by simpa using hj⟩

theorem finite_setOf_logHeight_le [Northcott (mulHeight₁ : K → ℝ)] (b : ℝ) :
    {P : Projectivization K (ι → K) | logHeight P ≤ b}.Finite := by
  refine (finite_setOf_mulHeight_le (Real.exp b)).subset fun P hP => ?_
  rw [Set.mem_setOf_eq, logHeight_eq_log_mulHeight] at hP
  rw [Set.mem_setOf_eq, ← Real.exp_log (mulHeight_pos P)]
  exact Real.exp_le_exp.mpr hP

scoped instance instNorthcottProjectivizationMulHeight [Northcott (mulHeight₁ : K → ℝ)] :
    Northcott (mulHeight (K := K) (ι := ι)) :=
  ⟨finite_setOf_mulHeight_le⟩

scoped instance instNorthcottProjectivizationLogHeight [Northcott (mulHeight₁ : K → ℝ)] :
    Northcott (logHeight (K := K) (ι := ι)) :=
  ⟨finite_setOf_logHeight_le⟩

end Projectivization
p2m_reactivate "P2MW.S_northcott_projMulHeight_numberField.NorthcottPort P2MW.S_northcott_projMulHeight_numberField.Projectivization"

namespace Projectivization
p2m_export "Projectivization" "mk_rep mulHeight_mk mk mulHeight rep_nonzero smul_def map logHeight_eq_log_mulHeight mulHeight_pos logHeight mk_eq_mk_iff'"
p2m_open "Projectivization"

open Height

private noncomputable def e₀ : Projectivization ℚ (Fin 2 → ℚ) :=
  mk ℚ ![1, 0] (by simp)

private noncomputable def e₁ : Projectivization ℚ (Fin 2 → ℚ) :=
  mk ℚ ![0, 1] (by simp)

lemma gate_mulHeight_mk_one_zero : mulHeight e₀ = 1 := by
  rw [e₀, mulHeight_mk]
  simp

theorem gate_height_le_sat_pair :
    e₀ ∈ {P : Projectivization ℚ (Fin 2 → ℚ) | mulHeight P ≤ 1} ∧
      e₁ ∈ {P : Projectivization ℚ (Fin 2 → ℚ) | mulHeight P ≤ 1} ∧ e₀ ≠ e₁ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.mem_setOf_eq, gate_mulHeight_mk_one_zero]
  · rw [Set.mem_setOf_eq, e₁, mulHeight_mk]
    simp
  · rw [e₀, e₁, Ne, mk_eq_mk_iff']
    rintro ⟨a, ha⟩
    have h0 := congrFun ha 0
    simp at h0

theorem gate_infinite_ambient : Set.Infinite (Set.univ : Set (Projectivization ℚ (Fin 2 → ℚ))) := by
  have hinj : Function.Injective fun q : ℚ => mk ℚ ![q, 1] (by simp) := by
    intro q q' h
    rw [mk_eq_mk_iff'] at h
    obtain ⟨a, ha⟩ := h
    have h1 := congrFun ha 1
    have h0 := congrFun ha 0
    simp only [Pi.smul_apply, smul_eq_mul] at h0 h1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      mul_one] at h0 h1
    rw [h1] at h0
    simpa using h0.symm
  exact Set.infinite_univ_iff.mpr (Infinite.of_injective _ hinj)

theorem gate_tuple_level_not_northcott :
    {x : Fin 2 → ℚ | Height.mulHeight x ≤ 1}.Infinite := by
  have hinj : Function.Injective fun c : ℚ => (![c, 0] : Fin 2 → ℚ) := by
    intro c c' h
    simpa using congrFun h 0
  refine Set.infinite_of_injective_forall_mem (f := fun c : ℚ => (![c, 0] : Fin 2 → ℚ)) hinj ?_
  intro c
  show Height.mulHeight (![c, 0] : Fin 2 → ℚ) ≤ 1
  rcases eq_or_ne c 0 with rfl | hc
  · norm_num [show (![0, 0] : Fin 2 → ℚ) = 0 by ext i; fin_cases i <;> simp]
  · have h : (![c, 0] : Fin 2 → ℚ) = c • ![1, 0] := by
      ext i
      fin_cases i <;> simp
    rw [h, Height.mulHeight_smul_eq_mulHeight _ hc]
    simp

end Projectivization
p2m_reactivate "P2MW.S_northcott_projMulHeight_numberField.NorthcottPort P2MW.S_northcott_projMulHeight_numberField.Projectivization"

theorem solution (K : Type) [Field K] [NumberField K] (ι : Type) [Finite ι] :
    Northcott (Projectivization.mulHeight : Projectivization K (ι → K) → ℝ) :=
  inferInstance

end
p2m_reactivate "P2MW.S_northcott_projMulHeight_numberField.NorthcottPort P2MW.S_northcott_projMulHeight_numberField.Projectivization"

end S_northcott_projMulHeight_numberField
end P2MW
export P2MW.S_northcott_projMulHeight_numberField (solution)
