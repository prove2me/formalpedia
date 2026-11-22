-- Prove2me | solution 1 for pac_lower_bound_member
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:35:52.726595+00:00
-- url     : https://prove2.me/submissions/28c00102-7887-429b-bdc1-176039327194

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
    (C : ConceptClass X Bool) (d : ℕ)
    (hd : VCDim X C = d) (ε δ : ℝ) (_hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hδ : 0 < δ) (_hδ1 : δ ≤ 1) (hδ2 : δ ≤ 1 / 7) (hd_pos : 1 ≤ d) (m : ℕ)
    (hm : m ∈ { m : ℕ | ∃ (L : BatchLearner X Bool),
      ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
        ∀ c ∈ C,
          MeasureTheory.Measure.pi (fun _ : Fin m => D)
            { xs : Fin m → X |
              D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
                ≤ ENNReal.ofReal ε }
            ≥ ENNReal.ofReal (1 - δ) }) :
    Nat.ceil ((d - 1 : ℝ) / 2) ≤ m := by
  -- Proof by contradiction: assume m < ⌈(d-1)/(64ε)⌉ and derive a violation
  -- of the PAC guarantee using the NFL counting argument on the shattered set.
  by_contra h_lt
  push Not at h_lt
  -- h_lt : m < ⌈(d-1)/(64ε)⌉
  -- Step 1: Extract shattered set T with |T| = d from VCDim X C = d.
  have ⟨T, hTshat, hTcard⟩ : ∃ T : Finset X, Shatters X C T ∧ T.card = d := by
    -- VCDim = d with d ≥ 1 → ∃ witness achieving the sup
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
  -- Step 2: Extract the learner L from the PAC membership hypothesis
  obtain ⟨L, hL⟩ := hm
  -- Step 3: T is nonempty (|T| = d ≥ 1)
  have hTne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h; simp [h] at hTcard; omega
  -- Step 4: Construct D = pushforward of uniform on ↥T to X.
  -- D is (1/d) · ∑_{x ∈ T} δ_x, a probability measure on X supported on T.
  --
  -- Step 5: The NFL double-averaging argument on the shattered set T.
  -- With 1/(64ε) constant, m < ⌈(d-1)/(64ε)⌉ → 2m < d = |T|.
  --
  -- PROOF ROUTE (same as pac_lower_bound_core):
  -- (1) 2m < d from h_lt and ε ≤ 1.
  -- (2) Double-averaging over f : ↥T → Bool (each realized by c_f ∈ C):
  --     pairing on unseen points gives E_f[D{error}] ≥ (d-m)/(2d) > 1 / 4.
  -- (3) By Fubini + averaging: ∃ c₀ ∈ C with E_xs[error(c₀)] > 1 / 4.
  -- (4) Reversed Markov: Pr[error ≤ 1 / 8] < 6 / 7.
  -- (5) For ε ≤ 1 / 8: contradiction with PAC at δ ≤ 1 / 7.
  --     For ε > 1 / 8: same, since 2m < d still holds.
  --
  -- SORRY: the double-averaging + reversed Markov measure bridge.
  -- Infrastructure: pairing counting (disagreement_sum_eq proved),
  -- finite sum averaging, reversed Markov on [0,1]-valued rv.
  suffices ∃ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D ∧
      ∃ c ∈ C,
        MeasureTheory.Measure.pi (fun _ : Fin m => D)
          { xs : Fin m → X |
            D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
              ≤ ENNReal.ofReal ε }
          < ENNReal.ofReal (1 - δ) by
    obtain ⟨D, hDprob, c, hcC, hfail⟩ := this
    exact not_le.mpr hfail (hL D hDprob c hcC)
  classical
  set d' := T.card with hd'_def
  have hd'_eq_d : d' = d := hTcard
  have h2m_lt_d : 2 * m < d' := by
    rw [hd'_eq_d]
    by_contra h_ge; push Not at h_ge
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
    _ < ENNReal.ofReal (1 - δ) := by
        apply ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num) |>.mpr
        linarith
