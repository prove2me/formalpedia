-- Prove2me | solution 1 for triangle_free_chromatic_number
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:19:07.620527+00:00
-- url     : https://prove2.me/submissions/de110778-7189-4cd1-a07d-08760a69c14f

import Mathlib

/- Source: Construction.lean -/
namespace Mycielski

def Adj {V : Type*} (G : SimpleGraph V) : Option (Bool × V) → Option (Bool × V) → Prop
  | none, none => False
  | none, some (b, _) => b = true
  | some (b, _), none => b = true
  | some (i, a), some (j, b) => G.Adj a b ∧ (i = false ∨ j = false)

def graph {V : Type*} (G : SimpleGraph V) : SimpleGraph (Option (Bool × V)) where
  Adj := Adj G
  symm := ⟨by
    intro u v huv
    cases u with
    | none => cases v <;> exact huv
    | some u =>
      cases v with
      | none => simpa [Adj] using huv
      | some v => exact ⟨huv.1.symm, huv.2.symm⟩⟩
  loopless := ⟨by
    intro u
    cases u <;> simp [Adj]⟩

instance {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (graph G).Adj := by
  intro u v
  change Decidable (Adj G u v)
  cases u <;> cases v <;> dsimp [Adj] <;> infer_instance

def TriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬∃ a b c : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj a c

end Mycielski

/- Source: TriangleFree.lean -/
namespace Mycielski

theorem triangleFree_graph {V : Type*} (G : SimpleGraph V)
    (hG : TriangleFree G) : TriangleFree (graph G) := by
  rintro ⟨a, b, c, hab, hbc, hac⟩
  cases a with
  | none =>
    cases b with
    | none => exact hab
    | some b =>
      cases c with
      | none => exact hac
      | some c =>
        have hb : b.1 = true := hab
        have hc : c.1 = true := hac
        change G.Adj b.2 c.2 ∧ (b.1 = false ∨ c.1 = false) at hbc
        simp [hb, hc] at hbc
  | some a =>
    cases b with
    | none =>
      cases c with
      | none => exact hbc
      | some c =>
        have ha : a.1 = true := hab
        have hc : c.1 = true := hbc
        change G.Adj a.2 c.2 ∧ (a.1 = false ∨ c.1 = false) at hac
        simp [ha, hc] at hac
    | some b =>
      cases c with
      | none =>
        have ha : a.1 = true := hac
        have hb : b.1 = true := hbc
        change G.Adj a.2 b.2 ∧ (a.1 = false ∨ b.1 = false) at hab
        simp [ha, hb] at hab
      | some c => exact hG ⟨a.2, b.2, c.2, hab.1, hbc.1, hac.1⟩

end Mycielski

/- Source: Chromatic.lean -/
namespace Mycielski

noncomputable def recolor {V α : Type*} (G : SimpleGraph V)
    (C : (graph G).Coloring α) : G.Coloring α := by
  classical
  refine SimpleGraph.Coloring.mk
    (fun v => if C (some (false, v)) = C none then C (some (true, v))
      else C (some (false, v))) ?_
  intro v w hvw
  have hoo : (graph G).Adj (some (false, v)) (some (false, w)) := ⟨hvw, Or.inl rfl⟩
  by_cases hv : C (some (false, v)) = C none
  · by_cases hw : C (some (false, w)) = C none
    · exact False.elim (C.valid hoo (hv.trans hw.symm))
    · simp only [hv, hw, if_pos]
      exact C.valid (show (graph G).Adj (some (true, v)) (some (false, w)) from
        ⟨hvw, Or.inr rfl⟩)
  · by_cases hw : C (some (false, w)) = C none
    · simp only [hv, hw, if_pos]
      exact C.valid (show (graph G).Adj (some (false, v)) (some (true, w)) from
        ⟨hvw, Or.inl rfl⟩)
    · simp only [hv, hw]
      exact C.valid hoo

theorem recolor_ne_apex {V α : Type*} (G : SimpleGraph V)
    (C : (graph G).Coloring α) (v : V) : recolor G C v ≠ C none := by
  classical
  change (if C (some (false, v)) = C none then C (some (true, v))
    else C (some (false, v))) ≠ C none
  split_ifs with h
  · exact C.valid (show (graph G).Adj (some (true, v)) none from rfl)
  · exact h

theorem chromatic_succ {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (hk : (k : ℕ∞) ≤ G.chromaticNumber) :
    ((k + 1 : ℕ) : ℕ∞) ≤ (graph G).chromaticNumber := by
  apply SimpleGraph.le_chromaticNumber_iff_coloring.mpr
  intro m C
  by_contra h
  have hmk : m ≤ k := by omega
  have hle : (m : ℕ∞) ≤ G.chromaticNumber :=
    (show (m : ℕ∞) ≤ k by exact_mod_cast hmk).trans hk
  have hsurj := SimpleGraph.le_chromaticNumber_iff_forall_surjective.mp hle (recolor G C)
  obtain ⟨v, hv⟩ := hsurj (C none)
  exact recolor_ne_apex G C v hv

end Mycielski

/- Source: Main.lean -/
namespace Mycielski

theorem exists_finite_graph (k : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (hD : DecidableRel G.Adj),
      (k : ℕ∞) ≤ G.chromaticNumber ∧ TriangleFree G := by
  induction k with
  | zero =>
    refine ⟨0, ⊥, inferInstance, ?_, ?_⟩
    · exact zero_le
    · simp [TriangleFree]
  | succ k ih =>
    obtain ⟨n, G, hD, hk, ht⟩ := ih
    let : DecidableRel G.Adj := hD
    let W := Option (Bool × Fin n)
    let H : SimpleGraph W := graph G
    let e : W ≃ Fin (Fintype.card W) := Fintype.equivFin W
    let G' : SimpleGraph (Fin (Fintype.card W)) := H.comap e.symm
    let f : H →g G' := {
      toFun := e
      map_rel' := by
        intro a b hab
        change H.Adj (e.symm (e a)) (e.symm (e b))
        simpa only [Equiv.symm_apply_apply] using hab
    }
    refine ⟨Fintype.card W, G', inferInstance, ?_, ?_⟩
    · exact (chromatic_succ G k hk).trans (SimpleGraph.chromaticNumber_mono_of_hom f)
    · rintro ⟨a, b, c, hab, hbc, hac⟩
      exact triangleFree_graph G ht ⟨e.symm a, e.symm b, e.symm c, hab, hbc, hac⟩

end Mycielski

set_option linter.unusedVariables false in
theorem solution :
    ∀ k : ℕ, ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (hD : DecidableRel G.Adj),
      @SimpleGraph.chromaticNumber (Fin n) G ≥ k ∧
      ¬∃ a b c : Fin n, G.Adj a b ∧ G.Adj b c ∧ G.Adj a c := by
  intro k
  exact Mycielski.exists_finite_graph k
