-- Prove2me | solution 1 for ja18_anoise46_direct_copy_pointwise_upper_bound_f213822f
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T19:28:10.028978+00:00
-- url     : https://prove2.me/submissions/95caacf5-42fc-47b3-a4ca-8192bb85d7ba

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_anoise34_dyadic_mark_cell_endpoint_error
import Theorems.Thm_AvramDividend_Classical_avram_anoise43_unit_dyadic_halfopen_cover
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
theorem solution
    {α : Type*} [DecidableEq α] (n : ℕ) (F : Finset α)
    (j : α → ℝ)
    (hF : ∀ u ∈ F, j u ∈ Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))) 
    (hDisj : (let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))); let C : ℕ → ℕ → Set ℝ := (fun k i => B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k) (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)); let w : ℕ → ℕ → ℝ := fun k i => -1 + (i : ℝ) / (2 : ℝ) ^ k; let q : ℕ → ℝ := (fun k => ∑ i ∈ Finset.range (2 ^ k), w k i * ((F.filter (fun u => j u ∈ C k i)).card : ℝ)); (∀ (k i l : ℕ) (hil : i ≠ l), Disjoint (C k i) (C k l))))
    (hUnique : (let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))); let C : ℕ → ℕ → Set ℝ := (fun k i => B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k) (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)); let w : ℕ → ℕ → ℝ := fun k i => -1 + (i : ℝ) / (2 : ℝ) ^ k; let q : ℕ → ℝ := (fun k => ∑ i ∈ Finset.range (2 ^ k), w k i * ((F.filter (fun u => j u ∈ C k i)).card : ℝ)); (∀ (k : ℕ) (u : α) (hu : u ∈ F), ∃ i : ℕ, i < 2 ^ k ∧ j u ∈ C k i ∧
        ∀ l : ℕ, l < 2 ^ k → j u ∈ C k l → l = i)))
    (hCountAsSum : (let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))); let C : ℕ → ℕ → Set ℝ := (fun k i => B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k) (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)); let w : ℕ → ℕ → ℝ := fun k i => -1 + (i : ℝ) / (2 : ℝ) ^ k; let q : ℕ → ℝ := (fun k => ∑ i ∈ Finset.range (2 ^ k), w k i * ((F.filter (fun u => j u ∈ C k i)).card : ℝ)); (∀ (k i : ℕ), ((F.filter (fun u => j u ∈ C k i)).card : ℝ) =
        ∑ u ∈ F, if j u ∈ C k i then (1 : ℝ) else 0)))
    (hReindex : (let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))); let C : ℕ → ℕ → Set ℝ := (fun k i => B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k) (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)); let w : ℕ → ℕ → ℝ := fun k i => -1 + (i : ℝ) / (2 : ℝ) ^ k; let q : ℕ → ℝ := (fun k => ∑ i ∈ Finset.range (2 ^ k), w k i * ((F.filter (fun u => j u ∈ C k i)).card : ℝ)); (∀ (k : ℕ), q k =
      ∑ u ∈ F, ∑ i ∈ Finset.range (2 ^ k),
        if j u ∈ C k i then w k i else 0)))
    : (let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))); let C : ℕ → ℕ → Set ℝ := (fun k i => B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k) (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)); let w : ℕ → ℕ → ℝ := fun k i => -1 + (i : ℝ) / (2 : ℝ) ^ k; let q : ℕ → ℝ := (fun k => ∑ i ∈ Finset.range (2 ^ k), w k i * ((F.filter (fun u => j u ∈ C k i)).card : ℝ)); (∀ (k : ℕ) (u : α) (hu : u ∈ F), |(∑ i ∈ Finset.range (2 ^ k),
          if j u ∈ C k i then w k i else 0) - j u| ≤
        (1 / 2 : ℝ) ^ k)) := by
    classical
    let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
    let C : ℕ → ℕ → Set ℝ := fun k i =>
        B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
          (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)
    let w : ℕ → ℕ → ℝ := fun k i => -1 + (i : ℝ) / (2 : ℝ) ^ k
    let q : ℕ → ℝ := fun k =>
        ∑ i ∈ Finset.range (2 ^ k), w k i * ((F.filter (fun u => j u ∈ C k i)).card : ℝ)
    let I : ℝ := ∑ u ∈ F, j u
    let e : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k * (F.card : ℝ)
    change ∀ (k : ℕ) (u : α) (hu : u ∈ F),
      |(∑ i ∈ Finset.range (2 ^ k),
          if j u ∈ C k i then w k i else 0) - j u| ≤
        (1 / 2 : ℝ) ^ k
    intro k u hu
    obtain ⟨i, hi, hCi, hOnly⟩ := hUnique k u hu
    have heq : (∑ l ∈ Finset.range (2 ^ k),
        if j u ∈ C k l then w k l else 0) = w k i := by
      calc
        (∑ l ∈ Finset.range (2 ^ k),
          if j u ∈ C k l then w k l else 0) =
            (if j u ∈ C k i then w k i else 0) := by
          apply Finset.sum_eq_single i
          · intro l hl hli
            have hn : ¬ j u ∈ C k l := by
              intro hCl
              exact hli (hOnly l (Finset.mem_range.mp hl) hCl)
            simp [hn]
          · intro hni
            exact (hni (Finset.mem_range.mpr hi)).elim
        _ = w k i := if_pos hCi
    rw [heq]
    have herr := avram_anoise34_dyadic_mark_cell_endpoint_error n k i (j u) hCi
    simpa only [w, abs_sub_comm, one_div_pow] using herr
end
