-- Prove2me | solution 1 for exists_fundamentalCycles_of_spanningTree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/66ff0054-f01c-5650-82e3-118187b06aa5

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_exists_fundamentalCycles_of_spanningTree

open Finset

namespace SolFlow

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (hd tl : E → V)

private def bd (c : E → ℤ) (w : V) : ℤ :=
  (∑ e with hd e = w, c e) - (∑ e with tl e = w, c e)

omit [Fintype V] [DecidableEq E] in
private lemma bd_sub (c d : E → ℤ) (w : V) :
    bd hd tl (fun e => c e - d e) w = bd hd tl c w - bd hd tl d w := by
  unfold bd; simp only [Finset.sum_sub_distrib]; ring

omit [Fintype V] in
private lemma bd_single (e₀ : E) (w : V) :
    bd hd tl (fun e => if e = e₀ then (1 : ℤ) else 0) w =
      (if w = hd e₀ then 1 else 0) - (if w = tl e₀ then 1 else 0) := by
  unfold bd
  simp only [Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]
  congr 1 <;> (split_ifs with h1 h2 <;> simp_all)

end SolFlow

open SolFlow in

theorem solution {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (hd tl : E → V) (T : Finset E)
    (hTpath : ∀ u v : V, ∃! c : E → ℤ, (∀ e ∉ T, c e = 0) ∧
      ∀ w, (∑ e with hd e = w, c e) - (∑ e with tl e = w, c e) =
        (if w = v then 1 else 0) - (if w = u then 1 else 0)) :
    ∃ Z : E → E → ℤ,
      (∀ j, ∀ w, (∑ e with hd e = w, Z j e) = (∑ e with tl e = w, Z j e)) ∧
      (∀ j ∈ Tᶜ, ∀ j' ∈ Tᶜ, Z j j' = if j = j' then 1 else 0) ∧
      (∀ j ∈ T, Z j = 0) ∧
      ∀ {A : Type*} [inst : AddCommGroup A] (f : E → A),
        (∀ w, (∑ e with hd e = w, f e) = (∑ e with tl e = w, f e)) →
        ∀ e, f e = ∑ j ∈ Tᶜ, Z j e • f j := by
  classical

  rcases isEmpty_or_nonempty V with hVe | hVne
  · haveI : IsEmpty E := ⟨fun e => hVe.elim (hd e)⟩
    exact ⟨fun _ _ => 0, fun _ _ => by simp, fun j _ => isEmptyElim j,
      fun j _ => isEmptyElim j, fun {A} _ f _ e => isEmptyElim e⟩
  obtain ⟨v₀⟩ := hVne

  set c : V → E → ℤ := fun v => (hTpath v₀ v).exists.choose with hcdef
  have hcspec : ∀ v, (∀ e ∉ T, c v e = 0) ∧
      ∀ w, bd hd tl (c v) w = (if w = v then 1 else 0) - (if w = v₀ then 1 else 0) :=
    fun v => (hTpath v₀ v).exists.choose_spec
  have hcuniq : ∀ v (c' : E → ℤ), (∀ e ∉ T, c' e = 0) →
      (∀ w, bd hd tl c' w = (if w = v then 1 else 0) - (if w = v₀ then 1 else 0)) →
      c' = c v :=
    fun v c' h1 h2 => (hTpath v₀ v).unique ⟨h1, h2⟩ (hcspec v)

  have hc0 : c v₀ = 0 := by
    refine (hcuniq v₀ 0 (fun _ _ => rfl) (fun w => ?_)).symm
    simp only [bd, Finset.sum_const_zero, sub_self, Pi.zero_apply]

  have hcsub_T : ∀ e e', e' ∉ T → c (hd e) e' - c (tl e) e' = 0 := fun e e' he' => by
    rw [(hcspec (hd e)).1 e' he', (hcspec (tl e)).1 e' he']; ring
  have hcsub_bd : ∀ e w, bd hd tl (fun e' => c (hd e) e' - c (tl e) e') w =
      (if w = hd e then 1 else 0) - (if w = tl e then 1 else 0) := fun e w => by
    rw [bd_sub hd tl, (hcspec (hd e)).2 w, (hcspec (tl e)).2 w]; ring

  have hkey : ∀ e ∈ T, ∀ e', c (hd e) e' - c (tl e) e' = if e' = e then (1 : ℤ) else 0 := by
    intro e heT

    have heq := (hTpath (tl e) (hd e)).unique
      (y₁ := fun e' => if e' = e then (1 : ℤ) else 0)
      (y₂ := fun e' => c (hd e) e' - c (tl e) e')
      ⟨fun e' he' => if_neg (fun (h : e' = e) => he' (h ▸ heT)), bd_single hd tl e⟩
      ⟨fun e' he' => hcsub_T e e' he', fun w => hcsub_bd e w⟩
    intro e'; exact (congrFun heq e').symm

  refine ⟨fun j e' => if j ∈ T then 0 else
    (if e' = j then 1 else 0) - (c (hd j) e' - c (tl j) e'), ?_, ?_, ?_, ?_⟩
  ·
    intro j w
    by_cases hjT : j ∈ T
    · simp only [hjT, if_true, Finset.sum_const_zero]
    · simp only [hjT, if_false]
      have hbd : bd hd tl (fun e' => (if e' = j then (1:ℤ) else 0) -
          (c (hd j) e' - c (tl j) e')) w = 0 := by
        rw [bd_sub hd tl, bd_single hd tl, hcsub_bd]; ring
      unfold bd at hbd; linarith [hbd]
  ·
    intro j hj j' hj'
    simp only [Finset.mem_compl] at hj hj'
    simp only [hj, if_false, hcsub_T j j' hj', sub_zero, eq_comm (a := j')]
  ·
    intro j hj; funext e'; simp only [hj, if_true]; rfl
  ·
    intro A _ f hf e

    have hZsum : ∀ e', (∑ j ∈ Tᶜ, (if j ∈ T then (0:ℤ) else
        (if e' = j then 1 else 0) - (c (hd j) e' - c (tl j) e')) • f j) =
        ∑ j ∈ Tᶜ, ((if e' = j then (1:ℤ) else 0) - (c (hd j) e' - c (tl j) e')) • f j := by
      intro e'; refine Finset.sum_congr rfl (fun j hj => ?_)
      simp only [Finset.mem_compl] at hj; simp only [hj, if_false]
    rw [hZsum e]

    set g : E → A := fun e' => f e' -
      ∑ j ∈ Tᶜ, ((if e' = j then (1:ℤ) else 0) - (c (hd j) e' - c (tl j) e')) • f j with hgdef
    suffices hge : g e = 0 by
      have := hge; rw [hgdef] at this; simp only at this
      exact sub_eq_zero.mp this

    have hgTc : ∀ e' ∈ Tᶜ, g e' = 0 := by
      intro e' he'
      simp only [Finset.mem_compl] at he'
      rw [hgdef]
      simp only
      rw [Finset.sum_eq_single e']
      · simp only [hcsub_T _ e' he', sub_zero, ite_true, one_smul, sub_self]
      · intro j hj hjne
        simp only [Finset.mem_compl] at hj
        rw [if_neg (Ne.symm hjne), hcsub_T j e' he']; simp
      · intro h; exact absurd (Finset.mem_compl.mpr he') h

    have hgK : ∀ w, (∑ e' with hd e' = w, g e') = (∑ e' with tl e' = w, g e') := by
      intro w
      simp only [hgdef, Finset.sum_sub_distrib]
      rw [hf w]
      congr 1

      rw [Finset.sum_comm (t := Tᶜ), Finset.sum_comm (s := univ.filter (tl · = w)) (t := Tᶜ)]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      simp only [← Finset.sum_smul]
      congr 1

      have hbdZ : bd hd tl (fun e' => (if e' = j then (1:ℤ) else 0) -
          (c (hd j) e' - c (tl j) e')) w = 0 := by
        rw [bd_sub hd tl, bd_single hd tl, hcsub_bd]; ring
      unfold bd at hbdZ; linarith

    by_cases heT : e ∈ T
    ·

      have step1 : g e = ∑ e' ∈ T, (c (hd e') e - c (tl e') e) • g e' := by
        have hind : g e = ∑ e' ∈ T, (if e' = e then (1:ℤ) else 0) • g e' := by
          simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', heT, if_true]
        rw [hind]
        refine Finset.sum_congr rfl (fun e' he' => ?_)
        rw [hkey e' he' e]
        simp only [@eq_comm _ e e']
      have step2 : (∑ e' ∈ T, (c (hd e') e - c (tl e') e) • g e') =
          ∑ v : V, c v e • ((∑ e' ∈ T with hd e' = v, g e') - (∑ e' ∈ T with tl e' = v, g e')) := by
        simp only [sub_smul, Finset.sum_sub_distrib, smul_sub, Finset.smul_sum]
        congr 1
        ·
          rw [← Finset.sum_fiberwise T hd (fun e' => c (hd e') e • g e')]
          refine Finset.sum_congr rfl (fun v _ => ?_)
          refine Finset.sum_congr rfl (fun e' he' => ?_)
          simp only [Finset.mem_filter] at he'; rw [he'.2]
        · rw [← Finset.sum_fiberwise T tl (fun e' => c (tl e') e • g e')]
          refine Finset.sum_congr rfl (fun v _ => ?_)
          refine Finset.sum_congr rfl (fun e' he' => ?_)
          simp only [Finset.mem_filter] at he'; rw [he'.2]
      have step3 : ∀ v, (∑ e' ∈ T with hd e' = v, g e') - (∑ e' ∈ T with tl e' = v, g e') =
          (∑ e' with hd e' = v, g e') - (∑ e' with tl e' = v, g e') := by
        intro v
        have hset1 : univ.filter (fun x => hd x = v ∧ x ∈ T) = T.filter (fun x => hd x = v) := by
          ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_comm]
        have hset2 : univ.filter (fun x => tl x = v ∧ x ∈ T) = T.filter (fun x => tl x = v) := by
          ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_comm]
        have hext1 : (∑ e' with hd e' = v, g e') = (∑ e' ∈ T with hd e' = v, g e') := by
          rw [← Finset.sum_filter_add_sum_filter_not (univ.filter (hd · = v)) (· ∈ T)]
          simp only [Finset.filter_filter]
          have h0 : (∑ e' ∈ univ with hd e' = v ∧ e' ∉ T, g e') = 0 :=
            Finset.sum_eq_zero (fun e' he' => by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he'
              exact hgTc e' (Finset.mem_compl.mpr he'.2))
          rw [h0, add_zero, hset1]
        have hext2 : (∑ e' with tl e' = v, g e') = (∑ e' ∈ T with tl e' = v, g e') := by
          rw [← Finset.sum_filter_add_sum_filter_not (univ.filter (tl · = v)) (· ∈ T)]
          simp only [Finset.filter_filter]
          have h0 : (∑ e' ∈ univ with tl e' = v ∧ e' ∉ T, g e') = 0 :=
            Finset.sum_eq_zero (fun e' he' => by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he'
              exact hgTc e' (Finset.mem_compl.mpr he'.2))
          rw [h0, add_zero, hset2]
        rw [hext1, hext2]
      rw [step1, step2]
      simp only [step3]
      refine Finset.sum_eq_zero (fun v _ => ?_)
      rw [hgK v, sub_self, smul_zero]
    · exact hgTc e (Finset.mem_compl.mpr heT)

end S_exists_fundamentalCycles_of_spanningTree
end P2MW
export P2MW.S_exists_fundamentalCycles_of_spanningTree (solution)
