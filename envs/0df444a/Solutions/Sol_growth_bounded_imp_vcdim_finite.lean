-- Prove2me | solution 1 for growth_bounded_imp_vcdim_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:37:43.978835+00:00
-- url     : https://prove2.me/submissions/5628a735-f975-49ab-b298-57b711d0631f

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u)
    (C : ConceptClass X Bool)
    (hgrowth : ∃ (d : ℕ), ∀ (m : ℕ), d ≤ m →
      GrowthFunction X C m ≤ ∑ i ∈ Finset.range (d + 1), Nat.choose m i) :
    VCDim X C < ⊤ := by
  -- M-Contrapositive: VCDim = ⊤ → growth bound fails.
  by_contra h
  push Not at h
  have hinf : VCDim X C = ⊤ := le_antisymm le_top h
  obtain ⟨d, hd⟩ := hgrowth
  -- Use iSup₂_eq_top to get a shattered set T with |T| > d
  have hvcdim_unbounded := (iSup₂_eq_top
    (fun (T : Finset X) (_ : Shatters X C T) => (T.card : WithTop ℕ))).mp
    (by rw [VCDim] at hinf; exact hinf)
  -- Get T with |T| > d, hence |T| ≥ d+1
  obtain ⟨T, hTshat, hTcard⟩ := hvcdim_unbounded d (WithTop.coe_lt_top d)
  -- hTcard : d < T.card (as WithTop ℕ)
  have hTcard' : d + 1 ≤ T.card := by exact_mod_cast WithTop.coe_lt_coe.mp hTcard
  -- Apply hd to m = T.card ≥ d:
  have hd_app := hd T.card (le_trans (Nat.le_succ d) hTcard')
  -- Step A: Shattering → GrowthFunction ≥ 2^T.card
  -- When T is shattered, all 2^|T| labelings are realized.
  -- GrowthFunction(C, |T|) = sSup over |T|-element sets of ncard(restrictions).
  -- Since T itself is |T|-element and shattered: ncard(restrictions of C to T) = 2^|T|.
  -- So GrowthFunction ≥ 2^|T|.
  have hgrowth_large : 2 ^ T.card ≤ GrowthFunction X C T.card := by
    -- GrowthFunction(m) = sSup over m-element sets S of ncard{restrictions of C to S}
    -- T is an T.card-element set that is shattered, so all 2^|T| labelings are realized.
    unfold GrowthFunction
    apply le_csSup
    · -- BddAbove: ncard of any subset of (↥S → Bool) ≤ 2^S.card = 2^T.card
      use 2 ^ T.card
      rintro n ⟨⟨S, hScard⟩, rfl⟩
      calc Set.ncard { f : ↥S → Bool | ∃ c ∈ C, ∀ x : ↥S, c ↑x = f x }
          ≤ Set.ncard (Set.univ : Set (↥S → Bool)) := Set.ncard_le_ncard (Set.subset_univ _)
        _ = Nat.card (↥S → Bool) := Set.ncard_univ _
        _ = Nat.card Bool ^ Nat.card ↥S := Nat.card_fun
        _ = 2 ^ S.card := by
            simp_all
        _ = 2 ^ T.card := by rw [hScard]
    · -- T witnesses this value in the range
      refine ⟨⟨T, rfl⟩, ?_⟩
      -- Need: ncard {f | ∃ c ∈ C, ...} = 2^T.card when T is shattered
      -- Shattering means every labeling is realized, so the set = Set.univ
      -- The goal after unfolding is about (fun S => ...) ⟨T, rfl⟩, so we simp/unfold first
      change Set.ncard { f : ↥T → Bool | ∃ c ∈ C, ∀ x : ↥T, c ↑x = f x } = 2 ^ T.card
      have hset_eq : { f : ↥T → Bool | ∃ c ∈ C, ∀ x : ↥T, c ↑x = f x } =
          (Set.univ : Set (↥T → Bool)) := by
        ext f; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact hTshat f
      rw [hset_eq, Set.ncard_univ, Nat.card_fun, Nat.card_eq_fintype_card,
          Fintype.card_bool, Nat.card_eq_fintype_card, Fintype.card_coe]
  -- Step B: ∑_{i≤d} C(T.card, i) < 2^T.card (since T.card > d, partial sum < full sum)
  have hsum_lt_pow : ∑ i ∈ Finset.range (d + 1), Nat.choose T.card i < 2 ^ T.card := by
    -- ∑_{i=0}^{T.card} C(T.card, i) = 2^T.card (sum_range_choose)
    -- Since d + 1 ≤ T.card, range(d+1) ⊊ range(T.card + 1), and missing terms > 0
    have hd_lt_Tcard : d < T.card := by omega
    -- Use: each C(m,i) ≤ C(m, m/2) (choose_le_middle), and there are ≤ d+1 terms
    -- Alternatively: partial sum < full sum = 2^T.card
    rw [← Nat.sum_range_choose T.card]
    exact Finset.sum_lt_sum_of_subset (i := T.card)
      (Finset.range_mono (by omega))
      (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr le_rfl))
      (fun h => absurd (Finset.mem_range.mp h) (by omega))
      (by rw [Nat.choose_self]; exact Nat.one_pos)
      (fun j _ _ => Nat.zero_le _)
  -- Step C: Contradiction
  -- Chain: 2^T.card ≤ GrowthFunction ≤ ∑ C(T.card,i) < 2^T.card → contradiction
  exact absurd (le_trans hgrowth_large hd_app) (not_le.mpr hsum_lt_pow)
