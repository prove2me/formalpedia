-- Prove2me | solution 1 for exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/f6cd9106-7f20-5cdb-a595-1f844d02877f

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport

open Set Metric Filter Topology

namespace M4aP3B
namespace Rows
namespace UniformSeminorm

variable {E E' V P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace P]

omit [FiniteDimensional ℝ E] [TopologicalSpace P] in

theorem norm_iteratedFDeriv_comp_affine_le {f : E' → V} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (a : E') (L : E →L[ℝ] E') (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun x => f (a + L x)) x‖ ≤ ‖iteratedFDeriv ℝ n f (a + L x)‖ * ‖L‖ ^ n := by
  have hfa : ContDiff ℝ (⊤ : ℕ∞) (fun z => f (a + z)) := hf.comp (contDiff_const.add contDiff_id)
  have hfun : (fun x => f (a + L x)) = (fun z => f (a + z)) ∘ L := rfl
  rw [hfun, L.iteratedFDeriv_comp_right hfa x (i := n) (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_left]
  calc ‖(iteratedFDeriv ℝ n f (a + L x)).compContinuousLinearMap fun _ => L‖
      ≤ ‖iteratedFDeriv ℝ n f (a + L x)‖ * ∏ _i : Fin n, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ n f (a + L x)‖ * ‖L‖ ^ n := by rw [Finset.prod_const, Finset.card_fin]

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in

theorem exists_pos_forall_mul_norm_le {Q : Set P} (hQ : IsCompact Q) {ℓ : P → E →L[ℝ] E'}
    (hℓ : ContinuousOn ℓ Q) (hinj : ∀ p ∈ Q, Function.Injective (ℓ p)) :
    ∃ m : ℝ, 0 < m ∧ ∀ p ∈ Q, ∀ x : E, m * ‖x‖ ≤ ‖ℓ p x‖ := by
  have hcpt : IsCompact (Q ×ˢ sphere (0 : E) 1) := hQ.prod (isCompact_sphere 0 1)
  have hcont : ContinuousOn (fun q : P × E => ‖ℓ q.1 q.2‖) (Q ×ˢ sphere (0 : E) 1) :=
    ((hℓ.comp continuousOn_fst fun q hq => hq.1).clm_apply continuousOn_snd).norm

  have hscale : ∀ p (x : E), x ≠ 0 → ‖ℓ p x‖ = ‖x‖ * ‖ℓ p (‖x‖⁻¹ • x)‖ := by
    intro p x hx
    rw [map_smul, norm_smul, norm_inv, norm_norm, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.2 hx),
      one_mul]
  have hsph : ∀ x : E, x ≠ 0 → ‖x‖⁻¹ • x ∈ sphere (0 : E) 1 := by
    intro x hx
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]
  rcases (Q ×ˢ sphere (0 : E) 1).eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun p hp x => ?_⟩
    by_cases hx : x = 0
    · simp [hx]
    · have : (p, ‖x‖⁻¹ • x) ∈ Q ×ˢ sphere (0 : E) 1 := ⟨hp, hsph x hx⟩
      rw [he] at this
      exact this.elim
  · obtain ⟨q₀, hq₀, hmin⟩ := hcpt.exists_isMinOn hne hcont
    have hpos : 0 < ‖ℓ q₀.1 q₀.2‖ := by
      refine norm_pos_iff.2 fun h0 => ?_
      have hq2 : q₀.2 ≠ 0 := by
        have := hq₀.2; rw [mem_sphere_zero_iff_norm] at this
        intro hz; rw [hz, norm_zero] at this; exact one_ne_zero this.symm
      exact hq2 (hinj q₀.1 hq₀.1 (by rw [h0, map_zero]))
    refine ⟨‖ℓ q₀.1 q₀.2‖, hpos, fun p hp x => ?_⟩
    by_cases hx : x = 0
    · simp [hx]
    · rw [hscale p x hx]
      have hm := hmin (a := (p, ‖x‖⁻¹ • x)) ⟨hp, hsph x hx⟩
      simp only at hm
      exact (mul_comm _ _).le.trans (mul_le_mul_of_nonneg_left hm (norm_nonneg x))

theorem exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport_impl
    {f : E' → V} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hsupp : HasCompactSupport f)
    {Q : Set P} (hQ : IsCompact Q) {c : P → E'} {ℓ : P → E →L[ℝ] E'}
    (hc : ContinuousOn c Q) (hℓ : ContinuousOn ℓ Q) (hinj : ∀ p ∈ Q, Function.Injective (ℓ p)) :
    (∃ S : Set E, IsCompact S ∧ ∀ p ∈ Q, tsupport (fun x => f (c p + ℓ p x)) ⊆ S) ∧
    ∀ k n : ℕ, ∃ C : ℝ, ∀ p ∈ Q, ∀ x : E,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => f (c p + ℓ p x)) x‖ ≤ C := by

  obtain ⟨R, hR⟩ := hsupp.isCompact.isBounded.subset_closedBall (0 : E')
  obtain ⟨Mc, hMc⟩ := hQ.exists_bound_of_continuousOn hc
  obtain ⟨m, hm, hml⟩ := exists_pos_forall_mul_norm_le (E' := E') hQ hℓ hinj
  obtain ⟨Ml, hMl⟩ := hQ.exists_bound_of_continuousOn hℓ
  set ρ : ℝ := (R + Mc) / m with hρ

  have hsuppS : ∀ p ∈ Q, tsupport (fun x => f (c p + ℓ p x)) ⊆ closedBall (0 : E) ρ := by
    intro p hp
    refine closure_minimal ?_ isClosed_closedBall
    intro x hx
    rw [Function.mem_support] at hx
    have hK : c p + ℓ p x ∈ closedBall (0 : E') R := hR (subset_tsupport _ (Function.mem_support.2 hx))
    rw [mem_closedBall_zero_iff] at hK ⊢
    have h1 : ‖ℓ p x‖ ≤ R + Mc := by
      have := norm_le_norm_add_norm_sub' (ℓ p x) (c p + ℓ p x)

      have h' : ‖ℓ p x‖ ≤ ‖c p + ℓ p x‖ + ‖c p‖ := by
        calc ‖ℓ p x‖ = ‖(c p + ℓ p x) - c p‖ := by rw [add_sub_cancel_left]
          _ ≤ ‖c p + ℓ p x‖ + ‖c p‖ := norm_sub_le _ _
      linarith [hMc p hp]
    have h2 := hml p hp x
    rw [hρ, le_div_iff₀ hm]
    linarith
  refine ⟨⟨closedBall 0 ρ, isCompact_closedBall 0 ρ, hsuppS⟩, fun k n => ?_⟩

  obtain ⟨Bn, hBn⟩ := (hsupp.iteratedFDeriv (𝕜 := ℝ) n).exists_bound_of_continuous
    (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  have hBn0 : 0 ≤ Bn := (norm_nonneg _).trans (hBn 0)
  refine ⟨|ρ| ^ k * (Bn * |Ml| ^ n), fun p hp x => ?_⟩
  have hC0 : 0 ≤ |ρ| ^ k * (Bn * |Ml| ^ n) := by positivity
  by_cases hx : x ∈ tsupport (fun x => f (c p + ℓ p x))
  ·
    have hxρ : ‖x‖ ≤ |ρ| := (mem_closedBall_zero_iff.1 (hsuppS p hp hx)).trans (le_abs_self ρ)
    have hD : ‖iteratedFDeriv ℝ n (fun x => f (c p + ℓ p x)) x‖ ≤ Bn * |Ml| ^ n := by
      refine (norm_iteratedFDeriv_comp_affine_le hf (c p) (ℓ p) n x).trans ?_
      exact mul_le_mul (hBn _) (pow_le_pow_left₀ (norm_nonneg _) ((hMl p hp).trans (le_abs_self _)) n)
        (by positivity) hBn0
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hxρ k) hD (norm_nonneg _) (by positivity)
  ·
    have h0 : iteratedFDeriv ℝ n (fun x => f (c p + ℓ p x)) x = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hx (tsupport_iteratedFDeriv_subset n h)
    rw [h0, norm_zero, mul_zero]
    exact hC0

theorem gate_empty {f : E' → V} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hsupp : HasCompactSupport f)
    (c : P → E') (ℓ : P → E →L[ℝ] E') :
    (∃ S : Set E, IsCompact S ∧ ∀ p ∈ (∅ : Set P), tsupport (fun x => f (c p + ℓ p x)) ⊆ S) ∧
    ∀ k n : ℕ, ∃ C : ℝ, ∀ p ∈ (∅ : Set P), ∀ x : E,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => f (c p + ℓ p x)) x‖ ≤ C :=
  exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport_impl hf hsupp isCompact_empty
    (continuousOn_empty _) (continuousOn_empty _) (fun _ h => h.elim)

end M4aP3B.Rows.UniformSeminorm

#print axioms M4aP3B.Rows.UniformSeminorm.exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport_impl
#print axioms M4aP3B.Rows.UniformSeminorm.gate_empty

theorem solution
    {E E' V P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace P] {f : E' → V} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hsupp : HasCompactSupport f)
    {Q : Set P} (hQ : IsCompact Q) {c : P → E'} {ℓ : P → E →L[ℝ] E'}
    (hc : ContinuousOn c Q) (hℓ : ContinuousOn ℓ Q) (hinj : ∀ p ∈ Q, Function.Injective (ℓ p)) :
    (∃ S : Set E, IsCompact S ∧ ∀ p ∈ Q, tsupport (fun x => f (c p + ℓ p x)) ⊆ S) ∧
    ∀ k n : ℕ, ∃ C : ℝ, ∀ p ∈ Q, ∀ x : E,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => f (c p + ℓ p x)) x‖ ≤ C := by
  first
    | exact M4aP3B.Rows.UniformSeminorm.exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport_impl hf hsupp hQ hc hℓ hinj
    | (apply M4aP3B.Rows.UniformSeminorm.exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport_impl <;> assumption)

end S_exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport
end P2MW
export P2MW.S_exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport (solution)
