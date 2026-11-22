-- Prove2me | solution 1 for mind_change_characterization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:42:13.864846+00:00
-- url     : https://prove2.me/submissions/eb6052bd-42d1-4a6e-be2f-d278b4635a1e

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Gold
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_MindChange
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_Gold

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u)
    (C : ConceptClass X Bool) :
    EXLearnable X C ↔
      ∃ (L : GoldLearner X Bool),
        ∀ (c : Concept X Bool), c ∈ C →
          ∀ (T : TextPresentation X c),
            MindChangeOrdinal X L c T.toDataStream < Ordinal.omega0 := by
  -- Bridge: dataUpTo T t = T.prefix (t + 1) (by rfl, both = (List.range (t+1)).map T.observe)
  have bridge : ∀ (T : DataStream X Bool) (t : ℕ),
      dataUpTo T t = T.prefix (t + 1) := fun _ _ => rfl
  constructor
  · -- Forward: EXLearnable → bounded MindChangeOrdinal
    intro ⟨L, hL⟩
    exact ⟨L, fun c hcC T => by
      obtain ⟨t₀, ht₀⟩ := hL c hcC T
      -- Convert EXLearnable convergence (dataUpTo) to prefix convergence
      have hpref : ∀ t ≥ t₀ + 1, L.conjecture (T.toDataStream.prefix t) = c := by
        intro t ht
        have h := ht₀ (t - 1) (by omega)
        rw [bridge] at h
        rwa [show t - 1 + 1 = t from by omega] at h
      -- Changes are finite: no changes after t₀ + 1 (learner stabilized on c)
      have hfin : { t : ℕ | L.conjecture (T.toDataStream.prefix t) ≠
                             L.conjecture (T.toDataStream.prefix (t + 1)) }.Finite :=
        Set.Finite.subset (Finset.range (t₀ + 1)).finite_toSet (fun t ht => by
          simp only [Set.mem_ofPred] at ht
          simp only [Finset.mem_coe, Finset.mem_range]
          by_contra hge; push Not at hge
          exact ht (by rw [hpref t (by omega), hpref (t + 1) (by omega)]))
      -- Unfold MindChangeOrdinal: Finite + correct convergence → (card : Ordinal) < omega0
      change MindChangeOrdinal X L c T.toDataStream < Ordinal.omega0
      unfold MindChangeOrdinal
      rw [dif_pos hfin, if_pos ⟨t₀ + 1, hpref⟩]
      exact Ordinal.natCast_lt_omega0 _⟩
  · -- Backward: bounded MindChangeOrdinal → EXLearnable
    intro ⟨L, hL⟩
    refine ⟨L, fun c hcC T => ?_⟩
    have hmco := hL c hcC T
    -- MindChangeOrdinal < omega0 forces the finite+correct branch
    unfold MindChangeOrdinal at hmco
    by_cases hfin : { t : ℕ | L.conjecture (T.toDataStream.prefix t) ≠
                               L.conjecture (T.toDataStream.prefix (t + 1)) }.Finite
    · rw [dif_pos hfin] at hmco
      by_cases hconv : ∃ t₀, ∀ t ≥ t₀, L.conjecture (T.toDataStream.prefix t) = c
      · -- Extract convergence and bridge back to dataUpTo
        obtain ⟨t₀, ht₀⟩ := hconv
        exact ⟨t₀, fun t ht => by
          rw [bridge]
          exact ht₀ (t + 1) (by omega)⟩
      · -- Incorrect convergence → MindChangeOrdinal = omega0, contradicts < omega0
        rw [if_neg hconv] at hmco; exact absurd hmco (lt_irrefl _)
    · -- Infinite changes → MindChangeOrdinal = omega0, contradicts < omega0
      rw [dif_neg hfin] at hmco; exact absurd hmco (lt_irrefl _)
