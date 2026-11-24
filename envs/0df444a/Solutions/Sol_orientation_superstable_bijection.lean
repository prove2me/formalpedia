-- Prove2me | solution 1 for orientation_superstable_bijection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:54:12.7128+00:00
-- url     : https://prove2.me/submissions/b89045ba-36d8-4e72-a3f3-e3b664985a64

module
public import Definitions.Def_ChipFiringWithLean_Config
public import Mathlib.Data.DFinsupp.Multiset
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Theorems.Thm_orientation_determined_by_indegrees
public import Theorems.Thm_maximal_superstable_orientation
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty


section
@[expose] public section
set_option trace.split.failure true
open Multiset Finset
private lemma orientation_to_config_indeg (G : CFGraph) (O : CFOrientation G) (q : G.V)
    (hO : acyclic_with_unique_source G O q) (v : G.V) :
    (orientation_to_config G O q hO).chips v =
    if v = q then 0 else (indeg G O v : ℤ) - 1 := by
  -- This follows directly from the definition of config_of_source
  simp only [orientation_to_config] at *
  -- Use the definition of config_of_source
  exact rfl
private theorem config_to_orientation_unique (G : CFGraph) (q : G.V)
    (c : Config G q)
    (O₁ O₂ : CFOrientation G)
    (hO₁ : acyclic_with_unique_source G O₁ q)
    (hO₂ : acyclic_with_unique_source G O₂ q)
    (h_eq₁ : orientation_to_config G O₁ q hO₁ = c)
    (h_eq₂ : orientation_to_config G O₂ q hO₂ = c) :
    O₁ = O₂ := by
  apply orientation_determined_by_indegrees O₁ O₂ hO₁.1 hO₂.1
  intro v

  have h_deg₁ := orientation_to_config_indeg G O₁ q hO₁ v
  have h_deg₂ := orientation_to_config_indeg G O₂ q hO₂ v

  have h_config_eq : (orientation_to_config G O₁ q hO₁).chips v =
                     (orientation_to_config G O₂ q hO₂).chips v := by
    rw [h_eq₁, h_eq₂]

  by_cases hv : v = q
  · -- Case v = q: Both vertices are sources, so indegree is 0
    rw [hv]
    rw [source_of_acyclic_with_unique_source hO₁, source_of_acyclic_with_unique_source hO₂]
  · -- Case v ≠ q: use vertex degree equality
    rw [h_deg₁, h_deg₂] at h_config_eq
    simp only [if_neg hv] at h_config_eq
    -- From config degrees being equal, show indegrees are equal
    have h := congr_arg (fun x => x + 1) h_config_eq
    simp only [sub_add_cancel] at h
    -- Use nat cast injection
    exact (Nat.cast_inj.mp h)
end
end

set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution (G : CFGraph) (q : G.V) :
    let α := {O : CFOrientation G // acyclic_with_unique_source G O q};
    let β := {c : Config G q // maximal_superstable G c};
    let f_raw : α → Config G q := λ O_sub => orientation_to_config G O_sub.val q O_sub.prop;
    let f : α → β := λ O_sub => ⟨f_raw O_sub, orientation_config_maximal G O_sub.val q O_sub.prop⟩;
    Function.Bijective f := by
  -- Define the domain and codomain types explicitly (can be removed if using let like above)
  let α := {O : CFOrientation G // acyclic_with_unique_source G O q}
  let β := {c : Config G q // maximal_superstable G c}
  -- Define the function f_raw : α → Config G q
  let f_raw : α → Config G q := λ O_sub => orientation_to_config G O_sub.val q O_sub.prop
  -- Define the function f : α → β, showing the result is maximal superstable
  let f : α → β := λ O_sub =>
    ⟨f_raw O_sub, orientation_config_maximal G O_sub.val q O_sub.prop⟩

  constructor
  -- Injectivity
  { -- Prove injective f using injective f_raw
    intros O₁_sub O₂_sub h_f_eq -- h_f_eq : f O₁_sub = f O₂_sub
    have h_f_raw_eq : f_raw O₁_sub = f_raw O₂_sub := by
      simp only [Subtype.mk.injEq] at h_f_eq; exact h_f_eq

    -- Reuse original injectivity proof structure, ensuring types match
    let ⟨O₁, h₁⟩ := O₁_sub
    let ⟨O₂, h₂⟩ := O₂_sub
    -- Define c, h_eq₁, h_eq₂ based on orientation_to_config directly
    let c := orientation_to_config G O₁ q h₁
    have h_eq₁ : orientation_to_config G O₁ q h₁ = c := rfl
    have h_eq₂ : orientation_to_config G O₂ q h₂ = c := by
      exact h_f_raw_eq.symm.trans h_eq₁

    apply Subtype.ext
    exact config_to_orientation_unique G q c O₁ O₂ h₁ h₂ h_eq₁ h_eq₂
  }

  -- Surjectivity
  { -- Prove Function.Surjective f
    unfold Function.Surjective
    intro y -- y should now have type β
    -- Access components using .val and .property
    let c_target : Config G q := y.val -- Explicitly type c_target
    let h_target_max_superstable := y.property

    -- Use the fact that every maximal superstable config comes from an orientation.
    rcases maximal_superstable_orientation G q c_target h_target_max_superstable with
      ⟨O, hO, h_config_eq_target⟩

    -- Construct the required subtype element x : α (the pre-image)
    let x : α := ⟨O, hO⟩

    -- Show that this x exists
    use x

    -- Show f x = y using Subtype.eq
    apply Subtype.ext
    -- Goal: (f x).val = y.val
    -- Need to show: f_raw x = c_target
    -- This is exactly h_config_eq_target
    exact h_config_eq_target
    -- Proof irrelevance handles the equality of the property components.
  }
