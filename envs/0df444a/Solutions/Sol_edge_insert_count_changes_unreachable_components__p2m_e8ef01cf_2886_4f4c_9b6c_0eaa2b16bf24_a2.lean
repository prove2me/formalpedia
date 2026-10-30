-- Prove2me | solution 1 for edge_insert_count_changes_unreachable_components__p2m_e8ef01cf_2886_4f4c_9b6c_0eaa2b16bf24_a2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T23:48:36.381119+00:00
-- url     : https://prove2.me/submissions/d0d656f3-7ede-4c6f-9041-431fe756858a

import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

open SimpleGraph

variable {V : Type} (K : SimpleGraph V) (u v : V)

def mergedRel (x y : V) : Prop :=
  K.Reachable x y ∨ (K.Reachable x u ∧ K.Reachable v y) ∨
    (K.Reachable x v ∧ K.Reachable u y)

lemma mergedRel_equivalence (hn : ¬ K.Reachable u v) : Equivalence (mergedRel K u v) := by
  constructor
  · intro x
    exact Or.inl (SimpleGraph.Reachable.refl x)
  · intro x y h
    rcases h with h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨h₂.symm, h₁.symm⟩)
    · exact Or.inr (Or.inl ⟨h₂.symm, h₁.symm⟩)
  · intro x y z hxy hyz
    rcases hxy with hxy | ⟨hx, hy⟩ | ⟨hx, hy⟩ <;>
      rcases hyz with hyz | ⟨hy', hz⟩ | ⟨hy', hz⟩
    · exact Or.inl (hxy.trans hyz)
    · exact Or.inr (Or.inl ⟨hxy.trans hy', hz⟩)
    · exact Or.inr (Or.inr ⟨hxy.trans hy', hz⟩)
    · exact Or.inr (Or.inl ⟨hx, hy.trans hyz⟩)
    · exact False.elim (hn ((hy.trans hy').symm))
    · exact Or.inl (hx.trans hz)
    · exact Or.inr (Or.inr ⟨hx, hy.trans hyz⟩)
    · exact Or.inl (hx.trans hz)
    · exact False.elim (hn (hy.trans hy'))

lemma inserted_reach_iff (hn : ¬ K.Reachable u v) (x y : V) :
    (K ⊔ SimpleGraph.edge u v).Reachable x y ↔ mergedRel K u v x y := by
  constructor
  · intro h
    apply Relation.reflTransGen_le_of_equivalence_of_le (mergedRel_equivalence K u v hn) _ x y
      (((K ⊔ SimpleGraph.edge u v).reachable_iff_reflTransGen x y).mp h)
    intro a b hab
    rcases (SimpleGraph.sup_adj K (SimpleGraph.edge u v) a b).mp hab with hk | he
    · exact Or.inl hk.reachable
    · rcases ((SimpleGraph.edge_adj u v a b).mp he).1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _, SimpleGraph.Reachable.refl _⟩)
      · exact Or.inr (Or.inr ⟨SimpleGraph.Reachable.refl _, SimpleGraph.Reachable.refl _⟩)
  · rintro (h | ⟨hx, hy⟩ | ⟨hx, hy⟩)
    · exact h.mono le_sup_left
    · exact (hx.mono le_sup_left).trans (((show (K ⊔ SimpleGraph.edge u v).Adj u v from
        (SimpleGraph.sup_adj _ _ _ _).mpr (Or.inr ((SimpleGraph.edge_adj _ _ _ _).mpr
          ⟨Or.inl ⟨rfl, rfl⟩, fun h ↦ hn (h ▸ SimpleGraph.Reachable.refl _)⟩))).reachable).trans
            (hy.mono le_sup_left))
    · exact (hx.mono le_sup_left).trans (((show (K ⊔ SimpleGraph.edge u v).Adj v u from
        (SimpleGraph.sup_adj _ _ _ _).mpr (Or.inr ((SimpleGraph.edge_adj _ _ _ _).mpr
          ⟨Or.inr ⟨rfl, rfl⟩, fun h ↦ hn (h ▸ SimpleGraph.Reachable.refl _)⟩))).reachable).trans
            (hy.mono le_sup_left))


lemma map_eq_iff (hn : ¬ K.Reachable u v) (c d : K.ConnectedComponent) :
    c.map (SimpleGraph.Hom.ofLE (le_sup_left : K ≤ K ⊔ SimpleGraph.edge u v)) =
      d.map (SimpleGraph.Hom.ofLE (le_sup_left : K ≤ K ⊔ SimpleGraph.edge u v)) ↔
    c = d ∨ (c = K.connectedComponentMk u ∧ d = K.connectedComponentMk v) ∨
      (c = K.connectedComponentMk v ∧ d = K.connectedComponentMk u) := by
  induction c using SimpleGraph.ConnectedComponent.ind with
  | h x =>
    induction d using SimpleGraph.ConnectedComponent.ind with
    | h y =>
      simp only [SimpleGraph.ConnectedComponent.map_mk, SimpleGraph.Hom.coe_ofLE,
        id_eq, SimpleGraph.ConnectedComponent.eq, inserted_reach_iff K u v hn,
        mergedRel]
      constructor <;> rintro (h | ⟨h, h'⟩ | ⟨h, h'⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨h, h'.symm⟩)
      · exact Or.inr (Or.inr ⟨h, h'.symm⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨h, h'.symm⟩)
      · exact Or.inr (Or.inr ⟨h, h'.symm⟩)


lemma collapse_card {α β : Type} [Fintype α] [Fintype β]
    (f : α → β) (a b : α) (hab : a ≠ b)
    (hsurj : Function.Surjective f)
    (hrel : ∀ x y, f x = f y ↔ x = y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a)) :
    Nat.card α = Nat.card β + 1 := by
  classical
  have hf : f a = f b := (hrel a b).2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
  let g : {x : α // x ≠ b} → β := fun x ↦ f x.1
  have hinj : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    rcases (hrel x.1 y.1).1 h with heq | ⟨_, hy⟩ | ⟨hx, _⟩
    · exact heq
    · exact (y.2 hy).elim
    · exact (x.2 hx).elim
  have hsur : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    by_cases hxb : x = b
    · exact ⟨⟨a, hab⟩, hf.trans (hxb ▸ hx)⟩
    · exact ⟨⟨x, hxb⟩, hx⟩
  let e : {x : α // x ≠ b} ≃ β := Equiv.ofBijective g ⟨hinj, hsur⟩
  have hc : Fintype.card α = Fintype.card (Option {x : α // x ≠ b}) :=
    (Fintype.card_congr (Equiv.optionSubtypeNe b)).symm
  rw [Fintype.card_option, Fintype.card_congr e] at hc
  simpa only [Nat.card_eq_fintype_card] using hc


theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (u v : V) (hne : u ≠ v) (hnreach : ¬ K.Reachable u v) :
    Nat.card K.ConnectedComponent =
      Nat.card (K ⊔ SimpleGraph.edge u v).ConnectedComponent + 1 := by
  classical
  let : Fintype K.ConnectedComponent := Fintype.ofFinite _
  let : Fintype (K ⊔ SimpleGraph.edge u v).ConnectedComponent := Fintype.ofFinite _
  exact collapse_card
    (SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE
      (le_sup_left : K ≤ K ⊔ SimpleGraph.edge u v)))
    (K.connectedComponentMk u) (K.connectedComponentMk v)
    (fun h ↦ hnreach (SimpleGraph.ConnectedComponent.exact h))
    (SimpleGraph.ConnectedComponent.surjective_map_ofLE le_sup_left)
    (map_eq_iff K u v hnreach)

