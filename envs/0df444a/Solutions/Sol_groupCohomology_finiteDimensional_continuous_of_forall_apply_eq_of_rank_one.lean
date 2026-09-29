-- Prove2me | solution 1 for groupCohomology.finiteDimensional_continuous_of_forall_apply_eq_of_rank_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/f7ed445f-99d6-575e-9b95-42739afef2fe

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Theorems.Thm_groupCohomology_finiteDimensional_continuous_of_shortExact
import Theorems.Thm_Rep_exists_devissage_of_not_simple
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finiteDimensional_continuous_of_forall_apply_eq_of_rank_one

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

open CategoryTheory

namespace P2mS26HFINtriv
open groupCohomology

variable {k G : Type u} [Field k] [Group G]

theorem devissage (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (P : Rep.{u} k G → Prop)
    (h0 : ∀ T : Rep.{u} k G, Subsingleton T → P T)
    (h1 : ∀ L : Rep.{u} k G, (∀ (g : G) (x : L), L.ρ g x = x) → Module.finrank k L = 1 → P L)
    (hmid : ∀ (A B C : Rep.{u} k G) (φ : A ⟶ B) (ψ : B ⟶ C), Function.Injective φ.hom →
      Function.Surjective ψ.hom → (∀ b : B, ψ.hom b = 0 ↔ ∃ a : A, φ.hom a = b) →
      (∀ (g : G) (b : B), B.ρ g b = b) → P A → P C → P B)
    (T : Rep.{u} k G) [FiniteDimensional k T] (hT : ∀ (g : G) (t : T), T.ρ g t = t) : P T := by
  classical

  suffices H : ∀ (n : ℕ) (T : Rep.{u} k G) [FiniteDimensional k T], (∀ (g : G) (t : T), T.ρ g t = t) →
      Module.finrank k T = n → P T from H _ T hT rfl
  intro n
  induction n using Nat.strong_induction_on with | _ n ih =>
  intro T _ hT hn
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · interval_cases n
    ·
      haveI : Subsingleton T := Module.finrank_zero_iff.1 hn
      exact h0 T inferInstance
    · exact h1 T hT hn
  ·
    have hpos : 0 < Module.finrank k T := by omega
    obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
    have hsmT : ∀ t : T, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ s : G, r s ∈ F.fixingSubgroup → T.ρ s t = t := fun t => ⟨⊥, inferInstance, fun s _ => hT s t⟩
    have hns : ¬ ∀ W : Submodule k T, (∀ (s : G) (v : T), v ∈ W → T.ρ s v ∈ W) → W = ⊥ ∨ W = ⊤ := by
      intro hall
      rcases hall (k ∙ v) (fun s w hw => by rw [hT s w]; exact hw) with hbot | htop
      · exact hv ((Submodule.span_singleton_eq_bot).1 hbot)
      · have h1 : Module.finrank k (k ∙ v) = 1 := finrank_span_singleton hv
        rw [htop, finrank_top] at h1
        omega
    obtain ⟨A, C, φ, ψ, -, -, hfdA, hfdC, hφ, hψ, hex, hA, hC, -, -, -⟩ :=
      Rep.exists_devissage_of_not_simple r T hsmT hns
    haveI := hfdA; haveI := hfdC
    have hAtriv : ∀ (g : G) (a : A), A.ρ g a = a := fun g a => hφ (by rw [Rep.hom_comm_apply, hT])
    have hCtriv : ∀ (g : G) (c : C), C.ρ g c = c := fun g c => by
      obtain ⟨b, rfl⟩ := hψ c
      rw [← Rep.hom_comm_apply, hT]
    exact hmid A T C φ ψ hφ hψ hex hT (ih _ (hn ▸ hA) A hAtriv rfl) (ih _ (hn ▸ hC) C hCtriv rfl)

theorem subsingleton_continuousH1 (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (T : Rep.{u} k G)
    [Subsingleton T] : Subsingleton (continuousH1 r T) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨c, -, hc⟩ := (mem_continuousH1_iff r T _).1 x.2
  obtain ⟨c', -, hc'⟩ := (mem_continuousH1_iff r T _).1 y.2
  have : c = c' := cocycles₁_ext fun _ => Subsingleton.elim _ _
  exact Subtype.ext (by rw [← hc, ← hc', this])

theorem subsingleton_continuousH2 (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (T : Rep.{u} k G)
    [Subsingleton T] : Subsingleton (continuousH2 r T) := by
  refine ⟨fun x y => ?_⟩
  induction x using Submodule.Quotient.induction_on with | _ a =>
  induction y using Submodule.Quotient.induction_on with | _ b =>
  have : a = b := Subtype.ext (funext fun _ => Subsingleton.elim _ _)
  rw [this]

end P2mS26HFINtriv

open P2mS26HFINtriv groupCohomology in
theorem solution {k G : Type u} [Field k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (T : Rep.{u} k G) [FiniteDimensional k T]
    (hT : ∀ (g : G) (t : T), T.ρ g t = t) :
    ((∀ L : Rep.{u} k G, (∀ (g : G) (x : L), L.ρ g x = x) → Module.finrank k L = 1 →
        FiniteDimensional k (groupCohomology.continuousH1 r L)) →
      FiniteDimensional k (groupCohomology.continuousH1 r T)) ∧
    ((∀ L : Rep.{u} k G, (∀ (g : G) (x : L), L.ρ g x = x) → Module.finrank k L = 1 →
        FiniteDimensional k (groupCohomology.continuousH2 r L)) →
      FiniteDimensional k (groupCohomology.continuousH2 r T)) := by
  have hsmT : ∀ t : T, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : G, r s ∈ F.fixingSubgroup → T.ρ s t = t := fun t => ⟨⊥, inferInstance, fun s _ => hT s t⟩
  refine ⟨fun hline => ?_, fun hline => ?_⟩
  · refine devissage r (fun X => FiniteDimensional k (continuousH1 r X)) (fun X _ => ?_) hline ?_ T hT
    · haveI := subsingleton_continuousH1 r X
      exact Module.Finite.of_finite
    · intro A B C φ ψ hφ hψ hex hB hA hC
      haveI := hA; haveI := hC
      exact (groupCohomology.finiteDimensional_continuous_of_shortExact r φ ψ hφ hψ hex
        (fun b => ⟨⊥, inferInstance, fun s _ => hB s b⟩)).2.1 inferInstance inferInstance
  · refine devissage r (fun X => FiniteDimensional k (continuousH2 r X)) (fun X _ => ?_) hline ?_ T hT
    · haveI := subsingleton_continuousH2 r X
      exact Module.Finite.of_finite
    · intro A B C φ ψ hφ hψ hex hB hA hC
      haveI := hA; haveI := hC
      exact (groupCohomology.finiteDimensional_continuous_of_shortExact r φ ψ hφ hψ hex
        (fun b => ⟨⊥, inferInstance, fun s _ => hB s b⟩)).2.2.2 inferInstance inferInstance

end S_groupCohomology_finiteDimensional_continuous_of_forall_apply_eq_of_rank_one
end P2MW
export P2MW.S_groupCohomology_finiteDimensional_continuous_of_forall_apply_eq_of_rank_one (solution)
