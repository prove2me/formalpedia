-- Prove2me | solution 1 for mme_CW_q6_primary_hash_bucket_structure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T20:51:22.748811+00:00
-- url     : https://prove2.me/submissions/be09b7d2-c2ba-4053-8fd3-0c241e79028e

import Definitions.Def_mme_CW_q6_primary_hash_bucket
import Theorems.Thm_mme_CW_q6_hash_bucket_coherence

open MME

/-- The literal retained hash bucket has the expected Z-count and degree
upper bounds and is closed under every supported retained mode mix. -/
theorem solution
    (N L G Xcount : ℕ)
    (hregular : CWQ6ExactAddressRegularity N L G)
    (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range ((4 * Xcount ^ 2 + 1) / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (b0 : ZMod (4 * Xcount ^ 2 + 1))
    (w : Fin (2 * N) → ZMod (4 * Xcount ^ 2 + 1)) :
    let E := cwQ6PrimaryHashBucket N L G Xcount S b0 w
    (E.image (fun e => e.1 2)).card ≤
        Nat.choose (2 * N) L * Nat.choose (2 * N - L) L ∧
    (∀ c ∈ E.image (fun e => e.1 2),
      (E.filter (fun e => e.1 2 = c)).card ≤ Nat.choose (2 * G) G) ∧
    ∀ ex ∈ E, ∀ ey ∈ E, ∀ ez ∈ E,
      CWQ6CoupledCoordinatewiseSupported
          (cwQ6CoupledMixedAddress ex.1 ey.1 ez.1) →
        ∃ e' ∈ E,
          e'.1 0 = ex.1 0 ∧
          e'.1 1 = ey.1 1 ∧
          e'.1 2 = ez.1 2 := by
  classical
  let E := cwQ6PrimaryHashBucket N L G Xcount S b0 w
  have hrawMem (e : CWQ6ExactCoupledAddress N L G) :
      e.1 ∈ cwQ6ExactAddresses N L G := by
    simp only [cwQ6ExactAddresses, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact e.2
  have hzImage : E.image (fun e => e.1 2) ⊆ cwQ6ExactZWords N L G := by
    intro c hc
    obtain ⟨e, heE, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_image.mpr ⟨e.1, hrawMem e, rfl⟩
  have himageCard : (E.image (fun e => e.1 2)).card ≤
      Nat.choose (2 * N) L * Nat.choose (2 * N - L) L := by
    exact (Finset.card_le_card hzImage).trans_eq hregular.z_word_card
  refine ⟨himageCard, ?_, ?_⟩
  · intro c hc
    have hcZ : c ∈ cwQ6ExactZWords N L G := hzImage hc
    let fiberImage : Finset (CWQ6CoupledAddress N) :=
      (E.filter (fun e => e.1 2 = c)).image (fun e => e.1)
    have hcardEq : fiberImage.card =
        (E.filter (fun e => e.1 2 = c)).card := by
      exact Finset.card_image_of_injective _ Subtype.val_injective
    have hfiberSubset : fiberImage ⊆
        (cwQ6ExactAddresses N L G).filter (fun e => e 2 = c) := by
      intro a ha
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_filter.mpr
        ⟨hrawMem e, (Finset.mem_filter.mp he).2⟩
    rw [← hcardEq]
    exact (Finset.card_le_card hfiberSubset).trans_eq
      (hregular.z_degree c hcZ)
  · intro ex hex ey hey ez hez hsupp
    have hex' : ∃ s ∈ S,
        cwQ6DoubledXHash b0 w (ex.1 0) =
            2 * (s : ZMod (4 * Xcount ^ 2 + 1)) ∧
        cwQ6DoubledYHash b0 w (ex.1 1) =
            2 * (s : ZMod (4 * Xcount ^ 2 + 1)) ∧
        cwQ6DoubledZHash b0 w (ex.1 2) =
            2 * (s : ZMod (4 * Xcount ^ 2 + 1)) := by
      simpa only [E, cwQ6PrimaryHashBucket, Finset.mem_filter,
        Finset.mem_univ, true_and] using hex
    have hey' : ∃ s ∈ S,
        cwQ6DoubledXHash b0 w (ey.1 0) =
            2 * (s : ZMod (4 * Xcount ^ 2 + 1)) ∧
        cwQ6DoubledYHash b0 w (ey.1 1) =
            2 * (s : ZMod (4 * Xcount ^ 2 + 1)) ∧
        cwQ6DoubledZHash b0 w (ey.1 2) =
            2 * (s : ZMod (4 * Xcount ^ 2 + 1)) := by
      simpa only [E, cwQ6PrimaryHashBucket, Finset.mem_filter,
        Finset.mem_univ, true_and] using hey
    have hez' : ∃ s ∈ S,
        cwQ6DoubledXHash b0 w (ez.1 0) =
            2 * (s : ZMod (4 * Xcount ^ 2 + 1)) ∧
        cwQ6DoubledYHash b0 w (ez.1 1) =
            2 * (s : ZMod (4 * Xcount ^ 2 + 1)) ∧
        cwQ6DoubledZHash b0 w (ez.1 2) =
            2 * (s : ZMod (4 * Xcount ^ 2 + 1)) := by
      simpa only [E, cwQ6PrimaryHashBucket, Finset.mem_filter,
        Finset.mem_univ, true_and] using hez
    obtain ⟨sx, hsx, hxx, _hxy, _hxz⟩ := hex'
    obtain ⟨sy, hsy, _hyx, hyy, _hyz⟩ := hey'
    obtain ⟨sz, hsz, _hzx, _hzy, hzz⟩ := hez'
    have hcoherent := mme_CW_q6_hash_bucket_coherence
      N Xcount S hSrange hSfree b0 w ex.1 ey.1 ez.1 hsupp
      sx sy sz hsx hsy hsz hxx hyy hzz
    let a : CWQ6CoupledAddress N :=
      cwQ6CoupledMixedAddress ex.1 ey.1 ez.1
    have haExact :
        CWQ6CoupledCoordinatewiseSupported a ∧
          ∀ i r : Fin 3,
            (Finset.univ.filter (fun j : Fin (2 * N) => a i j = r)).card =
              cwQ6CoupledMarginalMultiplicity N L G i r := by
      refine ⟨hsupp, ?_⟩
      intro i r
      fin_cases i
      · exact ex.2.2 (0 : Fin 3) r
      · exact ey.2.2 (1 : Fin 3) r
      · exact ez.2.2 (2 : Fin 3) r
    let e' : CWQ6ExactCoupledAddress N L G := ⟨a, haExact⟩
    have he'E : e' ∈ E := by
      change e' ∈ cwQ6PrimaryHashBucket N L G Xcount S b0 w
      simp only [cwQ6PrimaryHashBucket, Finset.mem_filter,
        Finset.mem_univ, true_and]
      refine ⟨sx, hsx, ?_, ?_, ?_⟩
      · simpa [e', a, cwQ6CoupledMixedAddress] using hxx
      · simpa [e', a, cwQ6CoupledMixedAddress, hcoherent.1] using hyy
      · simpa [e', a, cwQ6CoupledMixedAddress,
          hcoherent.1, hcoherent.2] using hzz
    refine ⟨e', he'E, ?_, ?_, ?_⟩ <;>
      rfl
