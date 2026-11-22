-- Prove2me | solution 1 for restriction_pattern_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:38:14.680792+00:00
-- url     : https://prove2.me/submissions/ce2e5ed0-5e8e-4441-93c4-66f33a6bd4f6

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Mathlib.Probability.Moments.SubGaussian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization

set_option autoImplicit true
@[expose] public section
public section
universe u v
open MeasureTheory ENNReal
theorem _root_.solution {X : Type u} [Infinite X]
    (C : ConceptClass X Bool) (c : Concept X Bool)
    (n : ℕ) (z : Fin n → X) :
    Set.ncard {p : Fin n → Bool | ∃ h ∈ C, ∀ i, p i = decide (h (z i) ≠ c (z i))} ≤
      GrowthFunction X C n := by
  classical
  let R : Set (Fin n → Bool) := {f | ∃ h ∈ C, ∀ i, f i = h (z i)}
  let ψ : (Fin n → Bool) → (Fin n → Bool) := fun f i => Bool.xor (f i) (c (z i))
  have hψ_inj : Function.Injective ψ := by
    intro f g hfg; funext i
    have hi := congr_fun hfg i; simp only [ψ] at hi
    revert hi; cases f i <;> cases g i <;> cases c (z i) <;> simp [Bool.xor]
  have hP_eq : {p : Fin n → Bool | ∃ h ∈ C, ∀ i, p i = decide (h (z i) ≠ c (z i))} = ψ '' R := by
    ext p; simp only [Set.mem_ofPred_eq, Set.mem_image, R, ψ]
    constructor
    · rintro ⟨h, hC, hp⟩
      refine ⟨fun i => h (z i), ⟨h, hC, fun i => rfl⟩, ?_⟩
      funext i; simp only [hp i]
      cases h (z i) <;> cases c (z i) <;> rfl
    · rintro ⟨f, ⟨h, hC, hf⟩, rfl⟩
      exact ⟨h, hC, fun i => by simp only [hf i]; cases h (z i) <;> cases c (z i) <;> rfl⟩
  rw [hP_eq, Set.ncard_image_of_injective R hψ_inj]
  let S₀ : Finset X := Finset.univ.image z
  have hS₀_card : S₀.card ≤ n :=
    (Finset.card_image_le).trans (by simp [Fintype.card_fin])
  obtain ⟨S, hS₀_sub, hS_card⟩ := Infinite.exists_superset_card_eq S₀ n hS₀_card
  have hz_mem : ∀ i : Fin n, z i ∈ S :=
    fun i => hS₀_sub (Finset.mem_image_of_mem z (Finset.mem_univ i))
  let R_S : Set (↥S → Bool) := {g | ∃ h ∈ C, ∀ x : ↥S, g x = h ↑x}
  let ρ : (↥S → Bool) → (Fin n → Bool) := fun g i => g ⟨z i, hz_mem i⟩
  have hR_sub : R ⊆ ρ '' R_S := by
    rintro f ⟨h, hC, hf⟩
    exact ⟨fun x => h ↑x, ⟨h, hC, fun x => rfl⟩, funext fun i => by simp only [ρ, hf i]⟩
  have hR_le_RS : R.ncard ≤ R_S.ncard :=
    (Set.ncard_le_ncard hR_sub (Set.toFinite _)).trans (Set.ncard_image_le (Set.toFinite R_S))
  have hR_S_eq : R_S.ncard =
      ({f : ↥S → Bool | ∃ c_1 ∈ C, ∀ x : ↥S, c_1 ↑x = f x} : Set _).ncard := by
    congr 1; ext f; exact ⟨fun ⟨h, hC, hf⟩ => ⟨h, hC, fun x => (hf x).symm⟩,
                           fun ⟨h, hC, hf⟩ => ⟨h, hC, fun x => (hf x).symm⟩⟩
  have hbdd : BddAbove (Set.range fun (T : {T : Finset X // T.card = n}) =>
      ({f : ↥T.val → Bool | ∃ c_1 ∈ C, ∀ x : ↥T.val, c_1 ↑x = f x} : Set _).ncard) := by
    refine ⟨2 ^ n, ?_⟩
    rintro _ ⟨T, rfl⟩
    calc Set.ncard _ ≤ Set.ncard (Set.univ : Set (↥T.val → Bool)) :=
            Set.ncard_le_ncard (Set.subset_univ _)
      _ = Nat.card (↥T.val → Bool) := Set.ncard_univ _
      _ = Fintype.card (↥T.val → Bool) := Nat.card_eq_fintype_card
      _ = 2 ^ T.val.card := by simp [Fintype.card_pi, Fintype.card_bool]
      _ = 2 ^ n := by rw [T.2]
  exact hR_le_RS.trans (hR_S_eq ▸ le_csSup hbdd ⟨⟨S, hS_card⟩, rfl⟩)
