-- Prove2me | solution 1 for tangent_deviation_bound_prob_from_two_sided_tail
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-22T06:36:51.383572+00:00
-- url     : https://prove2.me/submissions/ccbc869f-5bb8-4ebc-9e7b-f40ff2ad5d6d

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem solution
    {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r)
    (p t q bound : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    let EZ := bernoulliExpectation p (fun Ω => tangentSamplingDeviation Ω S p)
    bernoulliEventProb p
        (fun Ω => |tangentSamplingDeviation Ω S p - EZ| > t) ≤ q →
    EZ + t ≤ bound →
    bernoulliEventProb p
        (fun Ω => TangentSamplingDeviationBound Ω S p bound) ≥ 1 - q := by
  -- monotonicity of bernoulliEventProb under event implication
  have hmono_gen : ∀ (E F : Finset (Fin n1 × Fin n2) → Prop),
      (∀ Ω, E Ω → F Ω) →
      bernoulliEventProb p E ≤ bernoulliEventProb p F := by
    intro E F hEF
    unfold bernoulliEventProb
    apply Finset.sum_le_sum
    intro Ω _
    have hw : 0 ≤ bernoulliObservationWeight p Ω := by
      unfold bernoulliObservationWeight
      exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
    by_cases hE : E Ω
    · have hF : F Ω := hEF Ω hE
      simp [hE, hF]
    · by_cases hF : F Ω
      · simp [hE, hF]; exact hw
      · simp [hE, hF]
  -- total Bernoulli mass = 1, hence complement identity
  have hmass : ∑ Ω : Finset (Fin n1 × Fin n2), bernoulliObservationWeight p Ω = 1 := by
    classical
    have hkey := (Finset.prod_add (fun _ : Fin n1 × Fin n2 => p)
              (fun _ : Fin n1 × Fin n2 => (1 - p)) Finset.univ)
    have hlhs : ∏ _i : Fin n1 × Fin n2, (p + (1 - p)) = 1 := by simp
    rw [hlhs] at hkey
    have huniv : ∑ Ω : Finset (Fin n1 × Fin n2), bernoulliObservationWeight p Ω
        = ∑ s ∈ (Finset.univ : Finset (Fin n1 × Fin n2)).powerset,
            bernoulliObservationWeight p s := by
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext s; simp
    rw [huniv, hkey]
    apply Finset.sum_congr rfl
    intro s _
    unfold bernoulliObservationWeight
    have hpp : ∏ _i ∈ s, p = p ^ s.card := by rw [Finset.prod_const]
    have hcs : (Finset.univ \ s).card
        = Fintype.card (Fin n1 × Fin n2) - s.card := by rw [Finset.card_univ_diff]
    have hq2 : ∏ _i ∈ (Finset.univ \ s), (1 - p)
        = (1 - p) ^ (Fintype.card (Fin n1 × Fin n2) - s.card) := by
      rw [Finset.prod_const, hcs]
    rw [hpp, hq2]
  have hcompl_gen : ∀ (E : Finset (Fin n1 × Fin n2) → Prop),
      bernoulliEventProb p E + bernoulliEventProb p (fun Ω => ¬ E Ω) = 1 := by
    intro E
    unfold bernoulliEventProb
    rw [← Finset.sum_add_distrib, ← hmass]
    apply Finset.sum_congr rfl
    intro Ω _
    by_cases hE : E Ω <;> simp [hE]
  intro EZ htail hbudget
  have hcompl := hcompl_gen (fun Ω => |tangentSamplingDeviation Ω S p - EZ| > t)
  have hnt :
      bernoulliEventProb p
          (fun Ω => ¬ (|tangentSamplingDeviation Ω S p - EZ| > t)) ≥ 1 - q := by
    linarith [htail, hcompl]
  have hsub : ∀ Ω,
      (¬ (|tangentSamplingDeviation Ω S p - EZ| > t)) →
      TangentSamplingDeviationBound Ω S p bound := by
    intro Ω hΩ
    unfold TangentSamplingDeviationBound
    have habs : |tangentSamplingDeviation Ω S p - EZ| ≤ t := le_of_not_gt hΩ
    have hle : tangentSamplingDeviation Ω S p - EZ ≤ t :=
      le_trans (le_abs_self _) habs
    linarith [hbudget]
  have hmono := hmono_gen
    (fun Ω => ¬ (|tangentSamplingDeviation Ω S p - EZ| > t))
    (fun Ω => TangentSamplingDeviationBound Ω S p bound) hsub
  linarith [hnt, hmono]
