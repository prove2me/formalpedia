-- Prove2me | solution 1 for quadratic_neumann_all_distinct_middle_coefficient_entry_sup_pair_event_honest_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-01T10:00:06.259681+00:00
-- url     : https://prove2.me/submissions/da541dc8-5eb2-44b9-b5d4-f22f5df7a125

import Theorems.Thm_scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales
import Theorems.Thm_quadratic_neumann_all_distinct_middle_base_entry_sup_norm_bound_min_dim
import Theorems.Thm_quadratic_neumann_all_distinct_middle_base_frobenius_norm_bound_min_dim
import Theorems.Thm_quadratic_neumann_all_distinct_middle_coefficient_as_centered_scalar_fluctuation
import Theorems.Thm_quadratic_neumann_all_distinct_inner_coefficient_as_centered_scalar_fluctuation
import Theorems.Thm_quadratic_neumann_all_distinct_inner_base_entry_sup_norm_bound_min_dim
import Theorems.Thm_quadratic_neumann_all_distinct_inner_base_frobenius_norm_bound_min_dim
import Theorems.Thm_quadratic_neumann_all_distinct_inner_coefficient_uniform_two_term_event_honest_min_dim
import Theorems.Thm_bernoulli_uniform_bound_over_matrix_indices_from_shifted_pointwise_tails
import Theorems.Thm_bernoulli_pair_event_probability_from_marginal_and_conditional_lower_bounds_of_nonneg
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one
import Mathlib.Tactic

open MatrixCompletion

open scoped Classical BigOperators

/-!
# Honest-scale middle coefficient PAIR EVENT (node 2′) — FOUR-term `H`

Two-layer (`Ω₃` inner + `Ω₂` middle) de-la-Peña pair event for the all-distinct
middle coefficient `H_{ω₁}`, at the **honest** four-term scale obtained by
feeding the honest inner two-term `G_tt` (node 1′) through the Proved middle
base bounds and a Bernstein step over `Ω₂`.

Concretely, with product-Bernoulli probability `≥ 1 - ccoef·N^{-β}`,

  `‖H_{ω₁}‖∞ ≤ Ccoef · fourTerm`, where (`s := (β+2)logN/p`)

  `fourTerm = √s · (√(μ₀R/min)) · G_tt  +  s · (μ₀R/min) · G_tt`,

  `G_tt = √((β+4)logN/p)·(μ₁√(R/nn)·√(μ₀R/min))
        + ((β+4)logN/p)·(μ₁√(R/nn)·(μ₀R/min))`.

This SUPERSEDES the too-tight stub
`quadratic_neumann_all_distinct_middle_coefficient_entry_sup_pair_event_tight_min_dim`,
which hard-coded `innerBound = μ₁√(R/nn)·(μ₀R/min)` and thereby dropped the
`√(density)` factor of the random inner coefficient `G` (unsound by ~200–350×).

Source: Candès–Recht 2008, §6.3, PDF pp. 32--33, equation (6.23), Lemma 6.8
equations (6.22)--(6.23).
-/

namespace MatrixCompletion

/-- The honest inner two-term scale, as a function of the folded variables.  It
is the `bound` produced by node 1′ (with its `Cinner`). -/
private noncomputable def gTerm
    (n₁ n₂ r : ℕ) (μ₀ μ₁ β p : ℝ) : ℝ :=
  Real.sqrt (((β + 4) * Real.log (↑(max n₁ n₂))) / p) *
      (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
        Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
    (((β + 4) * Real.log (↑(max n₁ n₂))) / p) *
      (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
        (μ₀ * (r : ℝ) / (↑(min n₁ n₂))))

private lemma gTerm_nonneg
    {n₁ n₂ r : ℕ} {μ₀ μ₁ β p : ℝ}
    (hβ : 2 < β) (hμ₀ : 1 ≤ μ₀) (hμ₁ : 1 ≤ μ₁)
    (hlog : 0 ≤ Real.log (↑(max n₁ n₂))) (hp : 0 ≤ p) :
    0 ≤ gTerm n₁ n₂ r μ₀ μ₁ β p := by
  have hμ₀nn : 0 ≤ μ₀ := le_trans zero_le_one hμ₀
  have hμ₁nn : 0 ≤ μ₁ := le_trans zero_le_one hμ₁
  have hβ4 : 0 ≤ β + 4 := by linarith
  have hlogdiv : 0 ≤ ((β + 4) * Real.log (↑(max n₁ n₂))) / p :=
    div_nonneg (mul_nonneg hβ4 hlog) hp
  unfold gTerm
  have h1 : 0 ≤ Real.sqrt (((β + 4) * Real.log (↑(max n₁ n₂))) / p) := Real.sqrt_nonneg _
  positivity

end MatrixCompletion

/-- Honest-scale middle coefficient pair event (node 2′). -/
theorem solution :
    ∃ Ccoef ccoef : ℝ, 0 < Ccoef ∧ 0 < ccoef ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        bernoulliPairEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 Omega3 =>
              QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ccoef *
                  (Real.sqrt
                        (((β + 2) * Real.log (↑(max n₁ n₂))) /
                          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      (Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                        (Real.sqrt
                              (((β + 4) * Real.log (↑(max n₁ n₂))) /
                                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                            (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                              Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
                          (((β + 4) * Real.log (↑(max n₁ n₂))) /
                              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                            (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                              (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))))) +
                    (((β + 2) * Real.log (↑(max n₁ n₂))) /
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                        (Real.sqrt
                              (((β + 4) * Real.log (↑(max n₁ n₂))) /
                                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                            (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                              Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
                          (((β + 4) * Real.log (↑(max n₁ n₂))) /
                              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                            (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                              (μ₀ * (r : ℝ) / (↑(min n₁ n₂))))))))) ≥
          1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) := by
  classical
  -- suppliers
  obtain ⟨CentryInner, hCentryInner, hInnerEntry⟩ :=
    (quadratic_neumann_all_distinct_inner_base_entry_sup_norm_bound_min_dim :
      ∃ Centry : ℝ, 0 < Centry ∧ _)
  obtain ⟨CfroInner, hCfroInner, hInnerFrob⟩ :=
    (quadratic_neumann_all_distinct_inner_base_frobenius_norm_bound_min_dim :
      ∃ Cfro : ℝ, 0 < Cfro ∧ _)
  obtain ⟨Cinner, cinner, hCinner, hcinner, hInnerEvent⟩ :=
    quadratic_neumann_all_distinct_inner_coefficient_uniform_two_term_event_honest_min_dim
      CentryInner CfroInner hCentryInner hCfroInner
  obtain ⟨CentryMid, hCentryMid, hMidEntry⟩ :=
    (quadratic_neumann_all_distinct_middle_base_entry_sup_norm_bound_min_dim :
      ∃ Centry : ℝ, 0 < Centry ∧ _)
  obtain ⟨CfroMid, hCfroMid, hMidFrob⟩ :=
    (quadratic_neumann_all_distinct_middle_base_frobenius_norm_bound_min_dim :
      ∃ Cfro : ℝ, 0 < Cfro ∧ _)
  obtain ⟨Cbern, cbern, hCbern, hcbern, hBernstein⟩ :=
    scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales
  obtain ⟨Cuniform, cuniform, hCuniform, hcuniform, hUnionPrim⟩ :=
    bernoulli_uniform_bound_over_matrix_indices_from_shifted_pointwise_tails
      Cbern cbern hCbern hcbern
  -- final constants
  refine ⟨Cuniform * (Cinner * max CfroMid CentryMid),
    cuniform + cinner, by positivity, by positivity, ?_⟩
  intro β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1
  haveI : Nonempty (Fin n₁) := Fin.pos_iff_nonempty.mp hn₁
  haveI : Nonempty (Fin n₂) := Fin.pos_iff_nonempty.mp hn₂
  obtain ⟨hp_nonneg, hp_le_one⟩ := sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  set N : ℝ := (↑(max n₁ n₂) : ℝ) with hN
  set Cmax : ℝ := max CfroMid CentryMid with hCmax
  have hCmax_pos : 0 < Cmax := lt_max_of_lt_left (by positivity)
  have hμ₀nn : 0 ≤ μ₀ := le_trans zero_le_one hμ₀
  have hμ₁nn : 0 ≤ μ₁ := le_trans zero_le_one hμ₁
  have hβ2 : 2 < β + 2 := by linarith
  -- innerBound = Cinner · G_tt  (as node 1′ produces it)
  set G : ℝ := MatrixCompletion.gTerm n₁ n₂ r μ₀ μ₁ β p with hG
  have hlogN_nonneg : 0 ≤ Real.log (↑(max n₁ n₂)) := by
    apply Real.log_nonneg
    have : 1 ≤ max n₁ n₂ := le_trans hn₁ (Nat.le_max_left _ _)
    exact_mod_cast this
  have hG_nonneg : 0 ≤ G := by
    rw [hG]; exact MatrixCompletion.gTerm_nonneg hβ hμ₀ hμ₁ hlogN_nonneg hp_nonneg
  set innerBound : ℝ := Cinner * G with hinnerBound
  have hinnerBound_nonneg : 0 ≤ innerBound := by rw [hinnerBound]; positivity
  -- the honest four-term middle scale (target with Ccoef stripped)
  set fourTerm : ℝ :=
    Real.sqrt (((β + 2) * Real.log N) / p) *
        (Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) * G) +
      (((β + 2) * Real.log N) / p) *
        ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) * G) with hfourTerm
  -- middle raw base scales (with the middle base constants and innerBound)
  set midEntryRaw : ℝ :=
    CentryMid * innerBound * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) with hmidEntryRaw
  set midFrobRaw : ℝ :=
    CfroMid * innerBound * Real.sqrt (μ₀ * ((r : ℝ) / (↑(min n₁ n₂)))) with hmidFrobRaw
  have hmidEntryRaw_nonneg : 0 ≤ midEntryRaw := by rw [hmidEntryRaw]; positivity
  have hmidFrobRaw_nonneg : 0 ≤ midFrobRaw := by rw [hmidFrobRaw]; positivity
  -- inner marginal event over Ω₃ at innerBound = Cinner·G
  have hMarg :
      bernoulliEventProb p
          (fun Omega3 =>
            QuadraticAllDistinctInnerCoefficientBound Omega3 S p innerBound) ≥
        1 - cinner * Real.rpow N (-β) := by
    have hRepInner :
        ∀ (Omega3 : Finset (Fin n₁ × Fin n₂)) (w1 w2 : Fin n₁ × Fin n₂),
          quadraticAllDistinctInnerCoefficient Omega3 S p w1 w2 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega3 p
                (quadraticAllDistinctInnerBaseMatrix S w1 w2)) := by
      intro Omega3 w1 w2
      exact quadratic_neumann_all_distinct_inner_coefficient_as_centered_scalar_fluctuation
        Omega3 S p w1 w2
    have hEv :=
      hInnerEvent β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1
        hRepInner
        (fun w1 w2 => hInnerEntry n₁ n₂ r M μ₀ μ₁ S hn₁ hn₂ hr hμ₀ hμ₁ hA0 hA1 w1 w2)
        (fun w1 w2 => hInnerFrob n₁ n₂ r M μ₀ μ₁ S hn₁ hn₂ hr hμ₀ hμ₁ hA0 hA1 w1 w2)
    -- the node-1′ scale IS Cinner·G = innerBound (definitional after set-folding)
    have hscaleEq :
        innerBound =
          Cinner *
            (Real.sqrt
                (((β + 4) * Real.log (↑(max n₁ n₂))) /
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                  Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
              (((β + 4) * Real.log (↑(max n₁ n₂))) /
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                  (μ₀ * (r : ℝ) / (↑(min n₁ n₂))))) := by
      rw [hinnerBound, hG]
      show Cinner * MatrixCompletion.gTerm n₁ n₂ r μ₀ μ₁ β p = _
      unfold MatrixCompletion.gTerm
      rw [hp]
    rw [hscaleEq]
    simpa [hp, hN] using hEv
  -- CONDITIONAL: for each Ω₃ on the inner event, control every H_{ω₁} over Ω₂
  have hCond :
      ∀ Omega3 : Finset (Fin n₁ × Fin n₂),
        QuadraticAllDistinctInnerCoefficientBound Omega3 S p innerBound →
        bernoulliEventProb p
            (fun Omega2 =>
              QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S p
                (Cuniform * (Cinner * Cmax) * fourTerm)) ≥
          1 - cuniform * Real.rpow N (-β) := by
    intro Omega3 hInner
    -- middle base bounds (for this Ω₃, at innerBound)
    have hMEntry :
        ∀ w1 : Fin n₁ × Fin n₂,
          entrySupNorm (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1) ≤
            midEntryRaw := by
      intro w1
      rw [hmidEntryRaw]
      exact hMidEntry n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 Omega3 p innerBound
        hinnerBound_nonneg hInner w1
    have hMFrob :
        ∀ w1 : Fin n₁ × Fin n₂,
          frobeniusNorm (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1) ≤
            midFrobRaw := by
      intro w1
      rw [hmidFrobRaw]
      exact hMidFrob n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 Omega3 p innerBound
        hinnerBound_nonneg hInner w1
    -- per-w1 Bernstein tail (raw, at (β+2)) over Ω₂
    set midRawTwoTerm : ℝ :=
      Real.sqrt (((β + 2) * Real.log N) / p) * midFrobRaw +
        (((β + 2) * Real.log N) / p) * midEntryRaw with hmidRawTwoTerm
    have hPoint :
        ∀ w1 : Fin n₁ × Fin n₂,
          bernoulliEventProb p
              (fun Omega2 =>
                |quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S p w1| ≤
                  Cbern * midRawTwoTerm) ≥
            1 - cbern * Real.rpow N (-(β + 2)) := by
      intro w1
      have hRep :
          ∀ Omega : Finset (Fin n₁ × Fin n₂),
            (fun Omega =>
              quadraticAllDistinctMiddleCoefficient Omega Omega3 S p w1) Omega =
              matrixEntrySum
                (centeredSamplingFluctuation Omega p
                  (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1)) := by
        intro Omega
        exact quadratic_neumann_all_distinct_middle_coefficient_as_centered_scalar_fluctuation
          Omega Omega3 S p w1
      have hRaw :=
        hBernstein (β + 2) hβ2 n₁ n₂ m hn₁ hn₂ hm
          (fun Omega =>
            quadraticAllDistinctMiddleCoefficient Omega Omega3 S p w1)
          (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1)
          midEntryRaw midFrobRaw hRep (hMEntry w1) (hMFrob w1)
      simpa [hp, hN, hmidRawTwoTerm, mul_assoc] using hRaw
    -- single-coordinate union over w1  (β+2 → β)
    have hUnion :=
      hUnionPrim
        β p midRawTwoTerm hβ hp_nonneg hp_le_one n₁ n₂ hn₁ hn₂
        (fun w1 Omega2 =>
          quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S p w1)
        (by
          intro w1
          have h := hPoint w1
          rw [hN] at h
          exact h)
    -- weaken midRawTwoTerm ≤ Cinner·Cmax·fourTerm and rewrite to the middle bound
    have hRawTwoTerm_le :
        Cuniform * midRawTwoTerm ≤ Cuniform * (Cinner * Cmax * fourTerm) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hCuniform)
      have hlogfactor_nonneg :
          0 ≤ Real.sqrt (((β + 2) * Real.log N) / p) := Real.sqrt_nonneg _
      have hlogN : 0 ≤ Real.log N := by
        apply Real.log_nonneg; rw [hN]
        have : 1 ≤ max n₁ n₂ := le_trans hn₁ (Nat.le_max_left _ _)
        exact_mod_cast this
      have hβ2nn : (0 : ℝ) ≤ β + 2 := by linarith
      have hlogdiv_nonneg : 0 ≤ ((β + 2) * Real.log N) / p :=
        div_nonneg (mul_nonneg hβ2nn hlogN) hp_nonneg
      -- midFrobRaw = CfroMid·CfroInner·(√(μ₀R/min)·G) as scale (via innerBound=Cinner·G)
      have hfrobRaw_eq :
          midFrobRaw =
            CfroMid *
              (Cinner * (Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) * G)) := by
        rw [hmidFrobRaw, hinnerBound]
        have hmn_nonneg : 0 ≤ μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by positivity
        have hsqrt_eq :
            Real.sqrt (μ₀ * ((r : ℝ) / (↑(min n₁ n₂)))) =
              Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
          congr 1; ring
        rw [hsqrt_eq]; ring
      have hentryRaw_eq :
          midEntryRaw =
            CentryMid *
              (Cinner * ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) * G)) := by
        rw [hmidEntryRaw, hinnerBound]; ring
      have hCfroMul_le : CfroMid ≤ Cmax := le_max_left _ _
      have hCentryMul_le : CentryMid ≤ Cmax := le_max_right _ _
      have hFrobG_nonneg :
          0 ≤ Cinner * (Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) * G) := by positivity
      have hEntryG_nonneg :
          0 ≤ Cinner * ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) * G) := by positivity
      have hfrob_le :
          midFrobRaw ≤ Cmax * (Cinner * (Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) * G)) := by
        rw [hfrobRaw_eq]; exact mul_le_mul_of_nonneg_right hCfroMul_le hFrobG_nonneg
      have hentry_le :
          midEntryRaw ≤ Cmax * (Cinner * ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) * G)) := by
        rw [hentryRaw_eq]; exact mul_le_mul_of_nonneg_right hCentryMul_le hEntryG_nonneg
      calc midRawTwoTerm
          = Real.sqrt (((β + 2) * Real.log N) / p) * midFrobRaw +
              (((β + 2) * Real.log N) / p) * midEntryRaw := hmidRawTwoTerm
        _ ≤ Real.sqrt (((β + 2) * Real.log N) / p) *
                (Cmax * (Cinner * (Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) * G))) +
              (((β + 2) * Real.log N) / p) *
                (Cmax * (Cinner * ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) * G))) := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left hfrob_le hlogfactor_nonneg
              · exact mul_le_mul_of_nonneg_left hentry_le hlogdiv_nonneg
        _ = Cinner * Cmax *
              (Real.sqrt (((β + 2) * Real.log N) / p) *
                  (Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) * G) +
                (((β + 2) * Real.log N) / p) *
                  ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) * G)) := by ring
        _ = Cinner * Cmax * fourTerm := by rw [hfourTerm]
    -- monotone: uniform-abs event ⇒ middle coefficient bound
    have hFinalMono :
        bernoulliEventProb p
            (fun Omega2 =>
              ∀ w1 : Fin n₁ × Fin n₂,
                |quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S p w1| ≤
                  Cuniform * midRawTwoTerm) ≤
          bernoulliEventProb p
            (fun Omega2 =>
              QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S p
                (Cuniform * (Cinner * Cmax) * fourTerm)) := by
      refine bernoulli_event_probability_mono p _ _ hp_nonneg hp_le_one ?_
      intro Omega2 hAll
      intro w1
      calc |quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S p w1|
          ≤ Cuniform * midRawTwoTerm := hAll w1
        _ ≤ Cuniform * (Cinner * Cmax * fourTerm) := hRawTwoTerm_le
        _ = Cuniform * (Cinner * Cmax) * fourTerm := by ring
    exact le_trans hUnion hFinalMono
  -- pair lift  (marginal = inner over Ω₃ fails cinner; conditional = middle over Ω₂ fails cuniform)
  have hPairLift :=
    bernoulli_pair_event_probability_from_marginal_and_conditional_lower_bounds_of_nonneg
      (n₁ := n₁) (n₂ := n₂) p cinner cuniform (Real.rpow N (-β))
      (fun Omega3 => QuadraticAllDistinctInnerCoefficientBound Omega3 S p innerBound)
      (fun Omega2 Omega3 =>
        QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S p
          (Cuniform * (Cinner * Cmax) * fourTerm))
      hp_nonneg hp_le_one
      (by
        have : (0 : ℝ) ≤ Real.rpow N (-β) := Real.rpow_nonneg (by rw [hN]; positivity) _
        positivity)
      hMarg
      (fun Omega3 hM => hCond Omega3 hM)
  -- conclude: cCond+cMarg = cuniform+cinner
  have hgoal :
      bernoulliPairEventProb p
          (fun Omega2 Omega3 =>
            QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S p
              (Cuniform * (Cinner * Cmax) * fourTerm)) ≥
        1 - (cuniform + cinner) * Real.rpow N (-β) := hPairLift
  -- align fourTerm/G with the stated (inlined) scale
  have hGexpand :
      G =
        Real.sqrt
              (((β + 4) * Real.log (↑(max n₁ n₂))) / p) *
            (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
          (((β + 4) * Real.log (↑(max n₁ n₂))) / p) *
            (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) := by
    rw [hG]; rfl
  rw [hfourTerm, hGexpand] at hgoal
  rw [hp, hN] at hgoal
  convert hgoal using 4 <;> ring
