-- Prove2me | solution 1 for pac_lower_bound_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:42:56.507738+00:00
-- url     : https://prove2.me/submissions/e1097cd1-007e-4ad7-8d69-836da20d5850

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Theorems.Thm_nfl_counting_core
public import Theorems.Thm_pac_lower_bound_good_event_le_half

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u) [MeasurableSpace X] [MeasurableSingletonClass X]
    (C : ConceptClass X Bool) (d : ℕ) (hd_pos : 1 ≤ d)
    (hd : VCDim X C = d) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) :
    -- Any PAC learner needs at least ⌈(d-1)/(64ε)⌉ samples
    ∀ (L : BatchLearner X Bool) (mf : ℝ → ℝ → ℕ),
      (∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
        ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
          ∀ c ∈ C, let m := mf ε δ
          MeasureTheory.Measure.pi (fun _ : Fin m => D)
            { xs : Fin m → X |
              D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
                ≤ ENNReal.ofReal ε }
            ≥ ENNReal.ofReal (1 - δ)) →
      Nat.ceil ((d - 1 : ℝ) / 2) ≤ mf ε (1 / 7) := by
  -- Proof by contradiction: assume mf ε (1 / 7) < ⌈(d-1)/(2ε)⌉, derive violation
  -- of the PAC guarantee using NFL counting on the shattered set.
  intro L mf hpac
  by_contra h_lt
  push Not at h_lt
  -- h_lt : mf ε (1 / 7) < ⌈(d-1)/(2ε)⌉
  set m := mf ε (1 / 7) with hm_def
  -- Step 1: Extract shattered set T with |T| = d from VCDim X C = d.
  have ⟨T, hTshat, hTcard⟩ : ∃ T : Finset X, Shatters X C T ∧ T.card = d := by
    have hVCDim_eq : ⨆ (S : Finset X) (_ : Shatters X C S),
        (S.card : WithTop ℕ) = ↑d := hd
    have hle : ∀ S, Shatters X C S → S.card ≤ d := by
      intro S hS
      have : (S.card : WithTop ℕ) ≤ ↑d := by
        calc (S.card : WithTop ℕ)
            ≤ ⨆ (S : Finset X) (_ : Shatters X C S), (S.card : WithTop ℕ) :=
              le_iSup₂ (f := fun (S : Finset X) (_ : Shatters X C S) =>
                (S.card : WithTop ℕ)) S hS
          _ = ↑d := hVCDim_eq
      exact WithTop.coe_le_coe.mp this
    by_contra h_none
    push Not at h_none
    have hstrict : ∀ S, Shatters X C S → S.card ≤ d - 1 := by
      intro S hS; have := hle S hS; have := h_none S hS; omega
    have hbound : VCDim X C ≤ ↑(d - 1) := by
      apply iSup₂_le; simp_all
    rw [hd] at hbound
    have : d ≤ d - 1 := WithTop.coe_le_coe.mp hbound
    omega
  -- Step 2: Specialize PAC guarantee to δ = 1 / 7
  have hpac17 := hpac (1 / 7 : ℝ) (by norm_num : (0:ℝ) < 1 / 7) (by norm_num : (1:ℝ)/7 ≤ 1)
  -- hpac17 : ∀ D prob, ∀ c ∈ C, Pr[error ≤ ε] ≥ 6 / 7
  -- Step 3: Derive contradiction via NFL counting on shattered T.
  -- Suffices: ∃ D prob, ∃ c ∈ C, PAC guarantee fails at δ = 1 / 7.
  suffices ∃ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D ∧
      ∃ c ∈ C,
        MeasureTheory.Measure.pi (fun _ : Fin m => D)
          { xs : Fin m → X |
            D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
              ≤ ENNReal.ofReal ε }
          < ENNReal.ofReal (1 - 1 / 7) by
    obtain ⟨D, hDprob, c, hcC, hfail⟩ := this
    exact not_le.mpr hfail (hpac17 D hDprob c hcC)
  classical
  have hTne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h; simp [h] at hTcard; omega
  set d' := T.card with hd'_def
  have hd'_eq_d : d' = d := hTcard
  have h2m_lt_d : 2 * m < d' := by
    rw [hd'_eq_d]
    by_contra h_ge; push Not at h_ge
    -- h_ge : d ≤ 2 * m. From Nat.lt_ceil: (m : ℝ) < (d-1)/2, so 2m < d-1. Contradiction.
    have hm_real : (m : ℝ) < (d - 1 : ℝ) / 2 := Nat.lt_ceil.mp h_lt
    have hge_real : (d : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast h_ge
    linarith
  obtain ⟨_, c₀, hc₀C, _, hcount⟩ := nfl_counting_core hTshat h2m_lt_d L
  obtain ⟨D, hDprob, hgood_half⟩ :=
    pac_lower_bound_good_event_le_half (X := X) (T := T) hTne L m c₀ ε hε1
      (by simpa using hcount)
  refine ⟨D, hDprob, c₀, hc₀C, ?_⟩
  calc MeasureTheory.Measure.pi (fun _ : Fin m => D)
        { xs : Fin m → X |
          D { x | L.learn (fun i => (xs i, c₀ (xs i))) x ≠ c₀ x }
            ≤ ENNReal.ofReal ε }
      ≤ ENNReal.ofReal (1 / 2 : ℝ) := hgood_half
    _ < ENNReal.ofReal (1 - 1 / 7 : ℝ) := by
        exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num) |>.mpr (by norm_num)
