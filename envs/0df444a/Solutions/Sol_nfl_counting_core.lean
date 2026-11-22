-- Prove2me | solution 1 for nfl_counting_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:33:50.487311+00:00
-- url     : https://prove2.me/submissions/614dd423-f9da-413d-8216-d84c0583bccc

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
section
@[expose] public section
universe u v
section ERM_section
end ERM_section
section TrueError
end TrueError
section EmpiricalMeasureError
end EmpiricalMeasureError
section Consistency
end Consistency
section ConcentrationInfrastructure
end ConcentrationInfrastructure
section UniformConvergence
end UniformConvergence
section ConcentrationBridge
end ConcentrationBridge
section NFLCounting
private lemma per_sample_labeling_bound {α : Type*} [Fintype α] [DecidableEq α]
    (m : ℕ) (h2m : 2 * m < Fintype.card α)
    (xs : Fin m → α)
    (output : (α → Bool) → (α → Bool))
    (houtput : ∀ f f' : α → Bool, (∀ i : Fin m, f (xs i) = f' (xs i)) →
      output f = output f') :
    2 * (Finset.univ.filter fun f : α → Bool =>
      (Finset.univ.filter fun t : α => f t ≠ output f t).card * 4
      ≤ Fintype.card α).card
    ≤ Fintype.card (α → Bool) := by
  set d := Fintype.card α with hd_def
  set seen := Finset.image xs Finset.univ with hseen_def
  -- Define the flip involution: agree on seen, negate on unseen
  let flip : (α → Bool) → (α → Bool) := fun f t =>
    if t ∈ seen then f t else !f t
  have hflip_invol : ∀ f : α → Bool, flip (flip f) = f := by
    intro f; ext t; simp only [flip]; split_ifs <;> simp
  have hflip_seen : ∀ (f : α → Bool) (i : Fin m), flip f (xs i) = f (xs i) := by
    intro f i; simp only [flip]
    simp_all
  have hflip_output : ∀ f : α → Bool, output (flip f) = output f :=
    fun f => houtput (flip f) f (hflip_seen f)
  -- Key: for each pair (f, flip f), at most one is good.
  -- Reason: on unseen points, exactly one of f(t) and flip(f)(t) = !(f(t)) agrees
  -- with output(f)(t). So unseen disagrees are complementary.
  -- Total disagree(f) + disagree(flip f) ≥ |unseen| ≥ d - m > d/2.
  -- If both ≤ d/4, sum ≤ d/2. Contradiction.
  have hpair_bound : ∀ f : α → Bool,
      ¬((Finset.univ.filter fun t => f t ≠ output f t).card * 4 ≤ d ∧
        (Finset.univ.filter fun t => flip f t ≠ output (flip f) t).card * 4 ≤ d) := by
    intro f ⟨hgf, hgflip⟩
    rw [hflip_output] at hgflip
    -- Count: for each unseen t, exactly one of (f t ≠ h t) and (flip f t ≠ h t)
    -- holds, where h = output f. So total disagree ≥ |unseen|.
    -- We bound: disagree(f) + disagree(flip f) ≥ |unseen| ≥ d - m > d/2.
    -- But hgf + hgflip give sum ≤ d/2. Contradiction.
    have : d - m ≤ (Finset.univ.filter fun t => f t ≠ output f t).card +
        (Finset.univ.filter fun t => flip f t ≠ output f t).card := by
      -- For each unseen t: exactly one of f(t), flip(f)(t) disagrees with output(f)(t)
      -- So the combined filter covers all unseen points
      have hunseen_le : (Finset.univ \ seen).card ≤
          (Finset.univ.filter fun t => f t ≠ output f t).card +
          (Finset.univ.filter fun t => flip f t ≠ output f t).card := by
        calc (Finset.univ \ seen).card
            ≤ ((Finset.univ.filter fun t => f t ≠ output f t) ∪
               (Finset.univ.filter fun t => flip f t ≠ output f t)).card := by
              apply Finset.card_le_card
              intro t ht
              simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at ht
              simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
              -- t ∉ seen, so flip f t = !f t
              by_cases hft : f t ≠ output f t
              · left; exact hft
              · right
                push Not at hft
                change (if t ∈ seen then f t else !f t) ≠ output f t
                simp_all
          _ ≤ (Finset.univ.filter fun t => f t ≠ output f t).card +
              (Finset.univ.filter fun t => flip f t ≠ output f t).card :=
            Finset.card_union_le _ _
      have hseen_le : seen.card ≤ m := le_trans Finset.card_image_le (by simp)
      have hsdiff := Finset.card_sdiff_add_card_inter Finset.univ seen
      have hinter_le : (Finset.univ ∩ seen).card ≤ m :=
        le_trans (Finset.card_le_card Finset.inter_subset_right) hseen_le
      rw [Finset.card_univ] at hsdiff
      linarith
    omega
  -- Inject good set into pairs: for each good f, flip(f) is not good
  set S := Finset.univ.filter fun f : α → Bool =>
    (Finset.univ.filter fun t : α => f t ≠ output f t).card * 4 ≤ d
  set flipS := S.image flip
  have hdisjoint : Disjoint S flipS := by
    rw [Finset.disjoint_iff_ne]
    intro f hf g hg heq
    simp only [flipS, Finset.mem_image] at hg
    obtain ⟨g', hg'S, hg'eq⟩ := hg
    rw [← heq] at hg'eq
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hf hg'S
    have hgood_flip : (Finset.univ.filter fun t => flip g' t ≠
        output (flip g') t).card * 4 ≤ d := by
      rwa [hg'eq]
    exact hpair_bound g' ⟨hg'S, hgood_flip⟩
  have hflip_card : flipS.card = S.card := by
    apply Finset.card_image_of_injective
    intro a b hab; have := congr_arg flip hab; rwa [hflip_invol, hflip_invol] at this
  have hunion_le : S.card + flipS.card ≤ Fintype.card (α → Bool) := by
    rw [← Finset.card_union_of_disjoint hdisjoint]; exact Finset.card_le_univ _
  linarith
end NFLCounting
section NFLInfrastructure
end NFLInfrastructure
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution {X : Type u} {C : ConceptClass X Bool} {T : Finset X}
    (hT : Shatters X C T) {m : ℕ} (h2m : 2 * m < T.card)
    (L : BatchLearner X Bool) :
    ∃ (f₀ : ↥T → Bool),
      ∃ (c₀ : Concept X Bool), c₀ ∈ C ∧ (∀ t : ↥T, c₀ (↑t) = f₀ t) ∧
        2 * (Finset.univ.filter fun xs : Fin m → ↥T =>
          (Finset.univ.filter fun t : ↥T =>
            c₀ ((↑t : X)) ≠
              L.learn (fun i => ((↑(xs i) : X), c₀ (↑(xs i)))) (↑t)).card * 4
          ≤ T.card).card
        ≤ Fintype.card (Fin m → ↥T) := by
  classical
  set d := T.card with hd_def
  have hd_card : Fintype.card ↥T = d := Fintype.card_coe T
  -- For each f, shattering gives a witness c ∈ C with c|_T = f
  have hrealize : ∀ f : ↥T → Bool, ∃ c ∈ C, ∀ t : ↥T, c (↑t) = f t := hT
  -- Define: good(f, xs) iff the learner trained on f-labels at xs has error*4 ≤ d.
  -- We use f directly in the training data (not c_f), which is valid because
  -- c_f(↑(xs i)) = f(xs i) for the shattering witness.
  -- Step 1: Per-xs bound via per_sample_labeling_bound
  have hper_xs : ∀ xs : Fin m → ↥T,
      2 * (Finset.univ.filter fun f : ↥T → Bool =>
        (Finset.univ.filter fun t : ↥T =>
          f t ≠ (L.learn (fun i => ((↑(xs i) : X), f (xs i)))) (↑t)).card * 4
        ≤ d).card
      ≤ Fintype.card (↥T → Bool) := by
    intro xs
    have hbound := per_sample_labeling_bound m (by rwa [hd_card]) xs
      (fun f t => (L.learn (fun i => ((↑(xs i) : X), f (xs i)))) (↑t))
        (fun f f' hff' => by
          simp_all)
    rwa [hd_card] at hbound
  -- Step 2: By contradiction + pigeonhole to find f₀.
  -- The goal is ∃ f₀ c₀, c₀ ∈ C ∧ c₀|_T = f₀ ∧ 2 * count ≤ card.
  -- We use by_contra to get ∀ f₀ c₀, ... → card < 2 * count.
  by_contra h_all_bad
  push Not at h_all_bad
  -- For each f, use (hrealize f).choose as the witness. Since c(↑t) = f(t),
  -- the counting predicate with c₀ equals the counting predicate with f.
  have h_all_large : ∀ f : ↥T → Bool,
      Fintype.card (Fin m → ↥T) <
        2 * (Finset.univ.filter fun xs : Fin m → ↥T =>
          (Finset.univ.filter fun t : ↥T =>
            f t ≠ (L.learn (fun i => ((↑(xs i) : X), f (xs i)))) (↑t)).card * 4
          ≤ d).card := by
    intro f
    have hcf := (hrealize f).choose_spec.2
    have hlt := h_all_bad f (hrealize f).choose (hrealize f).choose_spec.1 hcf
    -- The statement uses c₀, we use f. Since c₀(↑t) = f(t) for all t,
    -- the filter predicates are equivalent.
    simp_all
  -- Step 3: Sum contradiction.
  -- Define good_count(f) = |{xs : error(f,xs)*4 ≤ d}|
  -- ∑_f 2*gc(f) > |↥T → Bool| * |Fin m → ↥T| (from h_all_large)
  -- ∑_f 2*gc(f) ≤ |Fin m → ↥T| * |↥T → Bool| (from double-counting + hper_xs)
  set gc : (↥T → Bool) → ℕ := fun f =>
    (Finset.univ.filter fun xs : Fin m → ↥T =>
      (Finset.univ.filter fun t : ↥T =>
        f t ≠ (L.learn (fun i => ((↑(xs i) : X), f (xs i)))) (↑t)).card * 4
      ≤ d).card with hgc_def
  have hsum_large : Fintype.card (↥T → Bool) * Fintype.card (Fin m → ↥T) <
      ∑ f : ↥T → Bool, 2 * gc f := by
    calc Fintype.card (↥T → Bool) * Fintype.card (Fin m → ↥T)
        = ∑ _f : ↥T → Bool, Fintype.card (Fin m → ↥T) := by
          simp [Finset.sum_const, Finset.card_univ]
      _ < ∑ f : ↥T → Bool, 2 * gc f := by
          apply Finset.sum_lt_sum
          · intro f _; exact le_of_lt (h_all_large f)
          · exact ⟨fun _ => false, Finset.mem_univ _, h_all_large _⟩
  -- Upper bound via double-counting: swap ∑_f ∑_xs to ∑_xs ∑_f
  -- Define the good predicate for the swap
  let P : (↥T → Bool) → (Fin m → ↥T) → Prop := fun f xs =>
    (Finset.univ.filter fun t : ↥T =>
      f t ≠ (L.learn (fun i => ((↑(xs i) : X), f (xs i)))) (↑t)).card * 4 ≤ d
  have hgc_P : ∀ f, gc f = (Finset.univ.filter fun xs => P f xs).card := by
    intro f; rfl
  have hsum_bounded : ∑ f : ↥T → Bool, 2 * gc f ≤
      Fintype.card (Fin m → ↥T) * Fintype.card (↥T → Bool) := by
    -- 2 * ∑_f gc(f) via Finset.mul_sum
    rw [show ∑ f : ↥T → Bool, 2 * gc f = 2 * ∑ f : ↥T → Bool, gc f
      from by rw [Finset.mul_sum]]
    -- Double counting: ∑_f gc(f) = ∑_f |{xs : P f xs}| = ∑_xs |{f : P f xs}|
    have hswap : ∑ f : ↥T → Bool, gc f =
        ∑ xs : Fin m → ↥T, (Finset.univ.filter fun f : ↥T → Bool => P f xs).card := by
      simp_rw [hgc_P, Finset.card_eq_sum_ones]
      rw [show ∑ f ∈ Finset.univ,
        ∑ _x ∈ Finset.univ.filter (fun xs : Fin m → ↥T => P f xs), 1 =
        ∑ f ∈ Finset.univ, ∑ xs ∈ Finset.univ,
          if P f xs then 1 else 0 from by
        congr 1; ext f; rw [Finset.sum_filter]]
      rw [show ∑ xs ∈ Finset.univ,
        ∑ _x ∈ Finset.univ.filter (fun f : ↥T → Bool => P f xs), 1 =
        ∑ xs ∈ Finset.univ, ∑ f ∈ Finset.univ,
          if P f xs then 1 else 0 from by
        congr 1; ext xs; rw [Finset.sum_filter]]
      exact Finset.sum_comm
    rw [hswap]
    -- 2 * ∑_xs |{f : P f xs}| = ∑_xs 2 * |{f : P f xs}| ≤ ∑_xs Fintype.card
    calc 2 * ∑ xs : Fin m → ↥T,
          (Finset.univ.filter fun f : ↥T → Bool => P f xs).card
        = ∑ xs : Fin m → ↥T,
          2 * (Finset.univ.filter fun f : ↥T → Bool => P f xs).card := by
          rw [Finset.mul_sum]
      _ ≤ ∑ _xs : Fin m → ↥T, Fintype.card (↥T → Bool) := by
          apply Finset.sum_le_sum; intro xs _; exact hper_xs xs
      _ = Fintype.card (Fin m → ↥T) * Fintype.card (↥T → Bool) := by
          simp [Finset.sum_const, Finset.card_univ]
  linarith
