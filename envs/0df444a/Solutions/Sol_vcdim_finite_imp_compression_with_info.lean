-- Prove2me | solution 1 for vcdim_finite_imp_compression_with_info
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:44:56.168464+00:00
-- url     : https://prove2.me/submissions/138fc985-e06b-4fed-868e-950d5ef6331d

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_FiniteVCApprox
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_FiniteSupportUC
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Compression
public import Theorems.Thm_supportAgreement_eq_one_sub_supportError
public import Theorems.Thm_vcdim_finite_imp_proper_finite_support_learner
public import Theorems.Thm_hypothesisEnvelope_sub
public import Theorems.Thm_roundtrip_blockHyp_eq_rep
public import Theorems.Thm_boolGamePayoff_eq_boolTestExpectation
public import Theorems.Thm_boolTestExpectation_empirical_eq_avg
public import Theorems.Thm_finite_support_vc_approx
public import Theorems.Thm_mwu_approx_minimax

section
@[expose] public section
open Finset
noncomputable section
universe u
attribute [local instance] Classical.propDecidable
private theorem boolTestExpectation_empirical_agreeTest_eq_avg {X : Type u} {T : ℕ}
    {HY : Finset (X → Bool)} [Fintype ↥HY] [DecidableEq ↥HY]
    (hT : 0 < T) (reps : Fin T → ↥HY) (c : X → Bool) (x : X) :
    boolTestExpectation (empiricalPMF hT reps) (agreeTest c x HY) =
      (∑ t : Fin T, if (reps t).val x = c x then (1 : ℝ) else 0) / T := by
  rw [boolTestExpectation_empirical_eq_avg]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  by_cases h : (↑(reps t) : X → Bool) x = c x <;> simp [agreeTest, h]
private lemma agreeTests_boolVCDim_le
    {X : Type u}
    (C : ConceptClass X Bool) (c : X → Bool) (Y : Finset X)
    (HY : Finset (X → Bool)) (hHY : ∀ h ∈ HY, h ∈ C)
    {d : ℕ} (hvc : VCDim X C ≤ ↑d) :
    (agreeTests c Y HY).boolVCDim ≤ 2 ^ (d + 1) - 1 := by
  classical
  simp only [Finset.boolVCDim, Finset.vcDim]
  apply Finset.sup_le
  intro T hT
  have hTs := Finset.mem_shatterer.mp hT
  -- By contradiction: if T.card ≥ 2^(d+1), extract d+1 shattered points in X.
  by_contra hlt
  push Not at hlt
  have hge : 2 ^ (d + 1) ≤ T.card := by omega
  -- Step 0: Embed (Fin (d+1) → Bool) into T.
  let eT := T.equivFin
  let eFun : (Fin (d + 1) → Bool) ≃ Fin (2 ^ (d + 1)) :=
    Fintype.equivOfCardEq (by simp [Fintype.card_bool, Fintype.card_fin])
  let eFin : Fin (2 ^ (d + 1)) ↪ Fin T.card := Fin.castLEEmb hge
  let eFinT : Fin T.card ≃ ↥T := eT.symm
  let embed : (Fin (d + 1) → Bool) → ↥T := eFinT ∘ eFin ∘ eFun
  have hembed_inj : Function.Injective embed := by
    intro a b hab; simp only [embed, Function.comp] at hab
    exact eFun.injective (eFin.injective (eFinT.injective hab))
  -- Step 1: For each j, define the half-set as the image of bitstrings with j-th bit true.
  let halfSet' (j : Fin (d + 1)) : Finset ↥HY :=
    (Finset.univ.filter (fun b : Fin (d + 1) → Bool => b j = true)).image
      (fun b => (embed b).val)
  have halfSet'_sub : ∀ j, halfSet' j ⊆ T := by
    intro j h hh
    simp only [halfSet', Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hh
    obtain ⟨b, _, rfl⟩ := hh
    exact (embed b).property
  -- Step 2: For each j, use shattering to find x_j ∈ Y.
  have hpoints : ∀ j : Fin (d + 1), ∃ x ∈ Y,
      ∀ h : ↥HY, h ∈ T →
        ((h.val x = c x) ↔ h ∈ halfSet' j) := by
    intro j
    obtain ⟨u, hu, hTu⟩ := hTs (halfSet'_sub j)
    simp only [boolFamilyToFinsetFamily, Finset.mem_image] at hu
    obtain ⟨f, hf, rfl⟩ := hu
    simp only [agreeTests, Finset.mem_image] at hf
    obtain ⟨x, hxY, rfl⟩ := hf
    refine ⟨x, hxY, fun h hmem => ?_⟩
    -- h ∈ halfSet' j ↔ h ∈ T ∩ u (from hTu)
    constructor
    · intro hagree
      have : h ∈ T ∩ Finset.univ.filter (fun h => agreeTest c x HY h = true) := by
        rw [Finset.mem_inter, Finset.mem_filter]
        exact ⟨hmem, Finset.mem_univ _, by simp [agreeTest, hagree]⟩
      exact hTu ▸ this
    · intro h_in_half
      have : h ∈ T ∩ Finset.univ.filter (fun h => agreeTest c x HY h = true) :=
        hTu ▸ h_in_half
      rw [Finset.mem_inter, Finset.mem_filter] at this
      simp only [agreeTest, decide_eq_true_eq] at this
      exact this.2.2
  choose x hxY hx using hpoints
  -- Step 3: The x_j are distinct.
  have hx_inj : Function.Injective x := by
    intro j k hjk
    by_contra hjk_ne
    let b0 : Fin (d + 1) → Bool := fun i => i == j
    let h0 : ↥T := embed b0
    -- h0.val ∈ halfSet' j
    have h0_in_j : h0.val ∈ halfSet' j := by
      simp only [halfSet', Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨b0, by simp [b0], rfl⟩
    -- h0.val ∉ halfSet' k
    have h0_nin_k : h0.val ∉ halfSet' k := by
      simp only [halfSet', Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      intro ⟨b', hb'k, hb'eq⟩
      have := hembed_inj (Subtype.ext hb'eq : embed b' = h0)
      rw [this] at hb'k; simp [b0] at hb'k
      exact hjk_ne hb'k.symm
    -- x j = x k gives: h.val (x j) = c (x j) ↔ h ∈ halfSet' j, same for k.
    have hj := (hx j h0.val h0.property).mpr h0_in_j
    simp_all
  -- Step 4: Build P = {x 0, ..., x d}.
  let P : Finset X := Finset.univ.image x
  have hP_card : P.card = d + 1 := by
    simp only [P, Finset.card_image_of_injective _ hx_inj,
      Finset.card_univ, Fintype.card_fin]
  -- Step 5: C shatters P (XOR trick).
  have hP_shatters : Shatters X C P := by
    intro g
    have hx_mem : ∀ j, x j ∈ P := fun j =>
      Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    -- b(j) = decide(g(x_j) = c(x_j)): absorbs the agree/disagree flip.
    let b : Fin (d + 1) → Bool := fun j =>
      decide (g ⟨x j, hx_mem j⟩ = c (x j))
    let h_wit : ↥T := embed b
    have h_wit_C : h_wit.val.val ∈ C := hHY _ h_wit.val.property
    refine ⟨h_wit.val.val, h_wit_C, fun ⟨y, hy⟩ => ?_⟩
    rw [Finset.mem_image] at hy
    obtain ⟨j, _, rfl⟩ := hy
    -- h_wit.val ∈ halfSet' j ↔ b j = true
    have h_wit_in_half_iff : h_wit.val ∈ halfSet' j ↔ b j = true := by
      simp only [halfSet', Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro ⟨b', hb'j, hb'eq⟩
        have := hembed_inj (Subtype.ext hb'eq : embed b' = h_wit)
        rw [this] at hb'j; exact hb'j
      · intro hbj; exact ⟨b, hbj, rfl⟩
    -- From hx: (h_wit.val.val (x j) = c (x j)) ↔ h_wit.val ∈ halfSet' j
    have hx_j := hx j h_wit.val h_wit.property
    -- Combine: (h_wit.val.val (x j) = c (x j)) ↔ (b j = true)
    have h_agree_iff : h_wit.val.val (x j) = c (x j) ↔ b j = true :=
      hx_j.trans h_wit_in_half_iff
    change h_wit.val.val (x j) = g ⟨x j, hx_mem j⟩
    by_cases heq : g ⟨x j, hx_mem j⟩ = c (x j)
    · have hbj : b j = true := by simp [b, heq]
      rw [heq]; exact h_agree_iff.mpr hbj
    · have hbj : b j = false := by
        simp only [b, decide_eq_false_iff_not]; exact heq
      have h_ne : h_wit.val.val (x j) ≠ c (x j) :=
        fun hc => Bool.noConfusion (show true = false from hbj ▸ (h_agree_iff.mp hc).symm)
      cases hc : c (x j) <;> cases hw : h_wit.val.val (x j) <;>
        cases hg : g ⟨x j, hx_mem j⟩ <;> simp_all
  -- Step 6: Contradicts VCDim X C ≤ d.
  have h_vc_ge : (P.card : WithTop ℕ) ≤ VCDim X C :=
    le_iSup₂_of_le P hP_shatters le_rfl
  rw [hP_card] at h_vc_ge
  have : (d + 1 : WithTop ℕ) ≤ (d : WithTop ℕ) := le_trans h_vc_ge hvc
  exact absurd this (by
    push Not; exact_mod_cast Nat.lt_succ_of_le le_rfl)
private theorem finalizeIncidenceScheme
    {X : Type u} {C : ConceptClass X Bool}
    (T K : ℕ)
    (compressCore : {m : ℕ} → (Fin m → X × Bool) → Finset (X × Bool) × IncidenceInfo T K)
    (blockHyp : Finset (X × Bool) → IncidenceInfo T K → Fin T → X → Bool)
    (rowHyp : {m : ℕ} → (S : Fin m → X × Bool) →
      (∃ c ∈ C, ∀ i : Fin m, c (S i).1 = (S i).2) → Fin T → X → Bool)
    (hT : 0 < T)
    (hsmall : ∀ {m : ℕ} (S : Fin m → X × Bool), (compressCore S).1.card ≤ K)
    (hsub : ∀ {m : ℕ} (S : Fin m → X × Bool), ↑(compressCore S).1 ⊆ Set.range S)
    (hagree : ∀ {m : ℕ} (S : Fin m → X × Bool)
      (hreal : ∃ c ∈ C, ∀ i : Fin m, c (S i).1 = (S i).2)
      (i : Fin m) (t : Fin T),
      blockHyp (compressCore S).1 (compressCore S).2 t (S i).1 = rowHyp S hreal t (S i).1)
    (hmajor : ∀ {m : ℕ} (S : Fin m → X × Bool)
      (hreal : ∃ c ∈ C, ∀ i : Fin m, c (S i).1 = (S i).2)
      (i : Fin m),
      ((∑ t : Fin T,
          if rowHyp S hreal t (S i).1 = (S i).2 then (1 : ℝ) else 0) / T) > (1 / 2 : ℝ)) :
    ∃ (k : ℕ) (cs : CompressionSchemeWithInfo0 X Bool C), cs.size = k := by
  exact ⟨_, mkIncidenceSchemeOfMajority
      (X := X) (C := C)
      T K compressCore blockHyp rowHyp hT hsmall hsub hagree hmajor, rfl⟩
private lemma good_on_support_gives_row_response
    {X : Type u} {C : ConceptClass X Bool}
    (L : ProperFiniteSupportLearner X C)
    (c : X → Bool) (hc : c ∈ C) (Y : Finset X)
    (HY : Finset (X → Bool))
    (hHY : HY = hypothesisEnvelope L c Y) :
    ∀ q : FinitePMF ↥Y, ∃ h : ↥HY,
      (2 : ℝ) / 3 ≤ ∑ y : ↥Y, q.prob y *
        (if decide (h.val (y : X) = c (y : X)) then (1 : ℝ) else 0) := by
  intro q
  obtain ⟨Z, hZY, hZcard, hZerr⟩ := L.good_on_support c hc Y q
  let h := L.learn (labeledSampleOfFinset c Z)
  have hh_mem : h ∈ HY := by
    rw [hHY]; exact Finset.mem_image.mpr ⟨Z, Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hZY, hZcard⟩, rfl⟩
  refine ⟨⟨h, hh_mem⟩, ?_⟩
  have hag := supportAgreement_eq_one_sub_supportError Y q h c
  simp only [decide_eq_true_eq] at *
  linarith
private theorem pointSupportNonempty {X : Type u} {m : ℕ} (S : Fin m → X × Bool)
    (hm : 0 < m) : Nonempty ↥(pointSupport S) :=
  ⟨⟨(S ⟨0, hm⟩).1, by simp [pointSupport, Finset.mem_image]⟩⟩
private theorem witness_mem_moranKernel {X : Type u} [DecidableEq X] {T : ℕ} (c : X → Bool)
    (getWitness : Fin T → Finset X) (t : Fin T) {x : X} (hx : x ∈ getWitness t) :
    (x, c x) ∈ Finset.univ.biUnion (fun t => (getWitness t).image (fun x => (x, c x))) := by
  exact Finset.mem_biUnion.mpr ⟨t, by simp, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
private theorem moran_yehudayoff_forward_construction
    (X : Type u) (C : ConceptClass X Bool)
    (_hne : C.Nonempty)
    (L : ProperFiniteSupportLearner X C)
    (hC : VCDim X C < ⊤)
    (_K : ℕ) :
    ∃ (k : ℕ) (cs : CompressionSchemeWithInfo0 X Bool C), cs.size = k := by
  classical
  have : DecidableEq X := Classical.decEq X
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hC)
  let s := L.sampleBound
  -- Parameter choice: ε_minimax = 1 / 12, ε_sparsify = 1 / 24.
  -- Sum = 1 / 12 + 1 / 24 = 1 / 8 < 1 / 6.
  -- Margin: 2 / 3 - 1 / 8 = 13 / 24 > 1 / 2. Strict majority guaranteed.
  -- The VC-approximation sample and minimax parameters are fixed so that the
  -- reconstruction vote has strict majority margin.
  obtain ⟨Tvc, hTvcPos, hVCApprox⟩ :=
    finite_support_vc_approx (2 ^ (d + 1) - 1) (1 / 24) (by norm_num)
  let Kreal := Tvc * s
  -- Decompose into 7 localized obligations for finalizeIncidenceScheme:
  -- 3 functions (compressCore, blockHyp, rowHyp) + 4 proofs (hsmall, hsub, hagree, hmajor)
  -- Extract the reps pipeline to a top-level function so hmajor can reference it.
  let mkReps : ∀ {m : ℕ} (S : Fin m → X × Bool)
      (hreal : ∃ c ∈ C, ∀ i : Fin m, c (S i).1 = (S i).2) (hm : 0 < m),
      Fin Tvc → ↥(hypothesisEnvelope L hreal.choose (pointSupport S)) := fun {m} S hreal hm =>
      let c := hreal.choose; let Y := pointSupport S
      haveI : Nonempty ↥Y := pointSupportNonempty S hm
      let HY := hypothesisEnvelope L c Y
      let hrow := good_on_support_gives_row_response L c hreal.choose_spec.1 Y HY rfl
      haveI : Nonempty ↥HY := let ⟨h, _⟩ := hrow (uniformPMF ↥Y); ⟨h⟩
      let M : ↥HY → ↥Y → Bool := fun h y => decide (h.val (y : X) = c (y : X))
      let mwu_result := mwu_approx_minimax M (2 / 3) (1 / 12) (by norm_num) hrow
      let p : FinitePMF ↥HY := mwu_result.choose
      let hvc_bound := agreeTests_boolVCDim_le C c Y HY
        (fun h hh => hypothesisEnvelope_sub L c Y h hh) (le_of_eq hd.symm)
      (hVCApprox (agreeTests c Y HY) hvc_bound p).choose
  let compressCore : {m : ℕ} → (Fin m → X × Bool) →
      Finset (X × Bool) × IncidenceInfo Tvc Kreal :=
    fun {m} S =>
      if hreal : ∃ c ∈ C, ∀ i : Fin m, c (S i).1 = (S i).2 then
        let c := hreal.choose
        let Y := pointSupport S
        if hm : 0 < m then
          haveI : Nonempty ↥Y := pointSupportNonempty S hm
          let HY := hypothesisEnvelope L c Y
          haveI : Nonempty ↥HY :=
            let hrow := good_on_support_gives_row_response L c hreal.choose_spec.1 Y HY rfl
            let ⟨h, _⟩ := hrow (uniformPMF ↥Y); ⟨h⟩
          let reps : Fin Tvc → ↥HY := mkReps S hreal hm
          -- For each representative, extract the witness subsample from hypothesisEnvelope.
          -- (getWitness + kernel + info)
          let getWitness : Fin Tvc → Finset X := fun t =>
            (Finset.mem_image.mp (reps t).property).choose
          let kernel : Finset (X × Bool) :=
            Finset.univ.biUnion (fun t => (getWitness t).image (fun x => (x, c x)))
          (kernel, fun t => encodeWitnessInfo kernel c Kreal (getWitness t))
        else
          (∅, fun _ => ∅)
      else
        (∅, fun _ => ∅)
  let blockHyp := moranBlockHyp L (T := Tvc) (K := Kreal)
  let rowHyp : {m : ℕ} → (S : Fin m → X × Bool) →
      (∃ c ∈ C, ∀ i : Fin m, c (S i).1 = (S i).2) → Fin Tvc → X → Bool :=
    fun {m} S _hreal t x => blockHyp (compressCore S).1 (compressCore S).2 t x
  have hsmall : ∀ {m : ℕ} (S : Fin m → X × Bool),
      (compressCore S).1.card ≤ Kreal := by
    intro m S; dsimp only [compressCore]
    split
    · next hreal =>
      split
      · next hm =>
        -- kernel.card ≤ Σ |image| ≤ Σ |witness| ≤ Σ s = Tvc*s = Kreal
        -- First, obtain the per-index witness bound generically
        have hwitness_bound : ∀ (h : ↥(hypothesisEnvelope L hreal.choose (pointSupport S))),
            (Finset.mem_image.mp h.property).choose.card ≤ s := fun h =>
          (Finset.mem_filter.mp (Finset.mem_image.mp h.property).choose_spec.1).2
        apply Finset.card_biUnion_le.trans
        apply le_trans _ (show Finset.univ.sum (fun _ : Fin Tvc => s) ≤ Kreal by
          simp [Finset.sum_const, Fintype.card_fin, Kreal])
        apply Finset.sum_le_sum; intro t _
        exact Finset.card_image_le.trans (hwitness_bound _)
      · next => -- m = 0 branch
        simp
    · next => -- ¬realizable branch
      simp
  have hsub : ∀ {m : ℕ} (S : Fin m → X × Bool),
      ↑(compressCore S).1 ⊆ Set.range S := by
    intro m S p hp; dsimp only [compressCore] at hp
    split at hp
    · next hreal =>
      split at hp
      · next hm =>
        -- p ∈ kernel = univ.biUnion (getWitness ·).image(...)
        rw [Finset.mem_coe] at hp
        rw [Finset.mem_biUnion] at hp
        obtain ⟨t, _, hp2⟩ := hp
        rw [Finset.mem_image] at hp2
        obtain ⟨x, hxw, hpx⟩ := hp2
        -- x ∈ getWitness t ⊆ Y = pointSupport S
        -- getWitness t ∈ boundedSubsamples (pointSupport S) s
        have hgw : ∀ (h : ↥(hypothesisEnvelope L hreal.choose (pointSupport S))),
            (Finset.mem_image.mp h.property).choose ⊆ pointSupport S := by
          intro h
          exact Finset.mem_powerset.mp
            (Finset.mem_filter.mp (Finset.mem_image.mp h.property).choose_spec.1).1
        have hxY : x ∈ pointSupport S := hgw _ hxw
        -- x ∈ pointSupport S = univ.image (S ·).1
        simp only [pointSupport, Finset.mem_image, Finset.mem_univ, true_and] at hxY
        obtain ⟨i, hi⟩ := hxY
        -- S i = p  (where hpx : (x, hreal.choose x) = p)
        rw [Set.mem_range]
        exact ⟨i, by
          rw [← hpx, Prod.mk.injEq]
          exact ⟨hi, (hreal.choose_spec.2 i).symm ▸ congrArg hreal.choose hi⟩⟩
      · next => simp at hp
    · next => simp at hp
  have hagree : ∀ {m : ℕ} (S : Fin m → X × Bool)
      (hreal : ∃ c ∈ C, ∀ i : Fin m, c (S i).1 = (S i).2)
      (i : Fin m) (t : Fin Tvc),
      blockHyp (compressCore S).1 (compressCore S).2 t (S i).1 =
        rowHyp S hreal t (S i).1 := by
    intro m S hreal i t; rfl
  have hmajor : ∀ {m : ℕ} (S : Fin m → X × Bool)
      (hreal : ∃ c ∈ C, ∀ i : Fin m, c (S i).1 = (S i).2)
      (i : Fin m),
      ((∑ t : Fin Tvc,
          if rowHyp S hreal t (S i).1 = (S i).2 then (1 : ℝ) else 0) / Tvc) >
        (1 / 2 : ℝ) := by
    intro m S hreal i
    have hm : 0 < m := Fin.pos i
    -- Phase 1: Roundtrip — decoded block hyp = raw representative.
    -- (`dsimp only [localLet]` works on goals, not hypotheses, so unfold in the goal first.)
    have h_kernel_labels : ∀ pair ∈ (compressCore S).1,
        pair.2 = hreal.choose pair.1 := by
      -- Unfold compressCore in the GOAL, resolve dite branches, THEN intro
      let reps := mkReps S hreal hm
      let getWitness : Fin Tvc → Finset X :=
        fun t => (Finset.mem_image.mp (reps t).property).choose
      dsimp only [compressCore]
      simp_all
    have hround : ∀ t : Fin Tvc,
        rowHyp S hreal t (S i).1 = (mkReps S hreal hm t).val (S i).1 := by
      intro t
      let c : X → Bool := hreal.choose
      let reps := mkReps S hreal hm
      let Y := pointSupport S
      let W : Finset X := (Finset.mem_image.mp (reps t).property).choose
      have hWspec : W ∈ boundedSubsamples Y L.sampleBound ∧
          L.learn (labeledSampleOfFinset c W) = (reps t).val := by
        simpa [W] using (Finset.mem_image.mp (reps t).property).choose_spec
      have hKbound : (compressCore S).1.card ≤ Kreal := hsmall S
      have hWker : ∀ x ∈ W, (x, c x) ∈ (compressCore S).1 := by
        intro x hx
        dsimp only [compressCore]
        simpa only [dif_pos hreal, dif_pos hm] using witness_mem_moranKernel c _ t hx
      have hrep : L.learn (labeledSampleOfFinset c W) = (reps t).val := hWspec.2
      have hlabels : ∀ p ∈ (compressCore S).1, p.2 = c p.1 := h_kernel_labels
      -- The roundtrip: use roundtrip_blockHyp_eq_rep
      have hrt := roundtrip_blockHyp_eq_rep
        (learn := fun {m} => L.learn)
        (kernel := (compressCore S).1) (c := c) (K := Kreal)
        (W := W) (h := (reps t).val)
        hKbound hWker hlabels hrep (x := (S i).1)
      -- rowHyp reduces definitionally to hrt's LHS once `(compressCore S).2 t` is
      -- rewritten to `encodeWitnessInfo (compressCore S).1 c Kreal W` (getWitness t = W).
      dsimp only [rowHyp]
      dsimp only [blockHyp, moranBlockHyp]
      have hinfo_eq : (compressCore S).2 t = encodeWitnessInfo (compressCore S).1 c Kreal W := by
        dsimp only [compressCore, c, reps, W]
        simp only [dif_pos hreal, dif_pos hm]
      rw [hinfo_eq]
      exact hrt
    -- Phase 2: Rewrite sum via if_congr (handles Decidable instance mismatch)
    have hlabel : (S i).2 = hreal.choose (S i).1 := (hreal.choose_spec.2 i).symm
    have hsum_eq : (∑ t : Fin Tvc,
        if rowHyp S hreal t (S i).1 = (S i).2 then (1 : ℝ) else 0) =
      (∑ t : Fin Tvc,
        if (mkReps S hreal hm t).val (S i).1 = hreal.choose (S i).1
        then (1 : ℝ) else 0) :=
      Finset.sum_congr rfl (fun t _ =>
        if_congr (by rw [hround t, hlabel]) rfl rfl)
    rw [hsum_eq]
    -- Phase 3: MWU + VC-approx chain gives ≥ 13 / 24 > 1 / 2
    suffices h_ge : (∑ t : Fin Tvc,
        if (mkReps S hreal hm t).val (S i).1 = hreal.choose (S i).1
        then (1 : ℝ) else 0) / ↑Tvc ≥ 13 / 24 by linarith
    -- Re-derive the pipeline guarantees (same objects as mkReps by let-transparency)
    have hYne : Nonempty ↥(pointSupport S) := pointSupportNonempty S hm
    let c' := hreal.choose
    let Y' := pointSupport S
    let HY' := hypothesisEnvelope L c' Y'
    let hrow' := good_on_support_gives_row_response L c' hreal.choose_spec.1 Y' HY' rfl
    have hHYne : Nonempty ↥HY' := let ⟨h, _⟩ := hrow' (uniformPMF ↥Y'); ⟨h⟩
    let M' : ↥HY' → ↥Y' → Bool := fun h y => decide (h.val (y : X) = c' (y : X))
    -- MWU: mixed strategy p with game value ≥ 7 / 12 at every column
    let mwu_result := mwu_approx_minimax M' (2 / 3) (1 / 12) (by norm_num) hrow'
    let p := mwu_result.choose
    have hp : ∀ y : ↥Y', (2 : ℝ) / 3 - 1 / 12 ≤ boolGamePayoff M' p y :=
      mwu_result.choose_spec
    -- VC-approx: sparse reps approximate p on agreement tests within 1 / 24
    let hvc_bound := agreeTests_boolVCDim_le C c' Y' HY'
      (fun h hh => hypothesisEnvelope_sub L c' Y' h hh) (le_of_eq hd.symm)
    let vc_result := hVCApprox (agreeTests c' Y' HY') hvc_bound p
    -- reps = mkReps S hreal hm (definitionally — same pipeline)
    -- hreps: approximation guarantee
    have hreps : ∀ a ∈ agreeTests c' Y' HY',
        |boolTestExpectation p a -
          boolTestExpectation (empiricalPMF hTvcPos (mkReps S hreal hm)) a| ≤ 1 / 24 := by
      -- vc_result.choose = mkReps S hreal hm by let-transparency
      intro a ha; convert vc_result.choose_spec a ha using 3
    -- (S i).1 ∈ Y' = pointSupport S
    have hxi_in_Y : (S i).1 ∈ Y' := by
      simp only [Y', pointSupport, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨i, rfl⟩
    -- agreeTest c' (S i).1 HY' ∈ agreeTests c' Y' HY'
    have hat_mem : agreeTest c' (S i).1 HY' ∈ agreeTests c' Y' HY' := by
      simp only [agreeTests, Finset.mem_image]; exact ⟨(S i).1, hxi_in_Y, rfl⟩
    -- Chain: minimax (7 / 12) → approx (1 / 24) → empirical ≥ 13 / 24
    have h_minimax : boolTestExpectation p (agreeTest c' (S i).1 HY') ≥ 7 / 12 := by
      have h_gp := hp ⟨(S i).1, hxi_in_Y⟩
      rw [boolGamePayoff_eq_boolTestExpectation] at h_gp
      have hfun : (fun h => M' h ⟨(S i).1, hxi_in_Y⟩) = agreeTest c' (S i).1 HY' := by
        ext h; simp only [M', agreeTest]
      rw [hfun] at h_gp; linarith
    have h_approx := hreps (agreeTest c' (S i).1 HY') hat_mem
    have h_emp_ge : boolTestExpectation (empiricalPMF hTvcPos (mkReps S hreal hm))
        (agreeTest c' (S i).1 HY') ≥ 13 / 24 := by
      have ⟨_, h_hi⟩ := abs_le.mp h_approx; linarith
    -- Bridge: empirical boolTestExpectation = the Prop-level sum / Tvc
    have h_emp_eq : boolTestExpectation (empiricalPMF hTvcPos (mkReps S hreal hm))
        (agreeTest c' (S i).1 HY') =
      (∑ t : Fin Tvc,
        if (mkReps S hreal hm t).val (S i).1 = c' (S i).1
        then (1 : ℝ) else 0) / ↑Tvc :=
      boolTestExpectation_empirical_agreeTest_eq_avg hTvcPos (mkReps S hreal hm) c' (S i).1
    linarith
  -- Package into the goal via finalizeIncidenceScheme
  exact finalizeIncidenceScheme Tvc Kreal compressCore blockHyp rowHyp
    hTvcPos hsmall hsub hagree hmajor
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section
universe u
attribute [local instance] Classical.propDecidable
theorem _root_.solution
    (X : Type u) (C : ConceptClass X Bool) (hC : VCDim X C < ⊤) :
    ∃ (k : ℕ) (cs : CompressionSchemeWithInfo0 X Bool C), cs.size = k := by
  by_cases hne : C.Nonempty
  · -- Nonempty C: the Moran-Yehudayoff construction
    obtain ⟨L, _⟩ := vcdim_finite_imp_proper_finite_support_learner X C hne hC
    -- Delegate to the Moran-Yehudayoff forward construction lemma.
    -- The kernel size bound is L.sampleBound (the construction uses a multiple of this).
    exact moran_yehudayoff_forward_construction X C hne L hC L.sampleBound
  · -- Empty C: realizability guard is always False
    refine ⟨1, ?_, ?_⟩
    · exact {
        Info := PUnit
        infoFinite := inferInstance
        compress := fun _ => (∅, PUnit.unit)
        reconstruct := fun _ _ _ => false
        kernelSize := 0
        compress_small := fun _ => by simp
        compress_sub := fun _ x hx => by simp at hx
        correct := fun {m} S hreal => by
          exfalso; obtain ⟨c, hcC, _⟩ := hreal
          exact hne ⟨c, hcC⟩
      }
    · simp [CompressionSchemeWithInfo.size]
