-- Prove2me | Theorems.Thm_BirthdayEntropy_Soundness_entropy_cell_counting
-- name    : BirthdayEntropy.Soundness.entropy_cell_counting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:49:53.836376+00:00
-- url     : https://prove2.me/theorems/6db64659-4ea7-4a44-8237-016053861e7c
-- title:
--   Lemma 4.2 — Entropy-weighted cell counting
-- statement:
--   Let $\Omega$ be a nonempty finite set, let $Q$ be uniform on it, and partition it by a deterministic finite-valued map $F$ into cells $\Omega_f$. Suppose $|\Omega_f|\le M_f$ on every occupied cell. Then
--   $$\log|\Omega|\le H_Q(F)+\mathbb E_Q\log M_F.$$
--   For every real ambient count $M$ and function $s$ such that $M_f\le M\exp(-s(f))$ on occupied cells, also
--   $$\log\frac M{|\Omega|}\ge\mathbb E_Qs(F)-H_Q(F).$$
--   Both conclusions belong to this item. Occupied cell bounds imply $M_f>0$ and, in the second conclusion, $M>0$. Empty cells have zero mass and are not read. This abstract lemma relates a partition's cardinalities to its actual entropy.
--
--   Differences from the source:
--   - encoding: a finite partition of Omega with a uniform law → a nonempty finite subset of an ambient finite type with a deterministic finite-valued map; reason: every finite partition has this encoding and Q is computed, not supplied
--   - generalization: upper bounds required for every cell → upper bounds required only for occupied cells; reason: empty cells have zero probability and can be discarded; the source hypotheses imply the stated ones
-- source:
--   Alexandru Popa, Entropy-Weighted Soundness for Multi-Answer Birthday Graphs, STOC 2027 submission #907 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/907.pdf, Lemma 4.2, PDF pp7 / printed pp6

import Mathlib
import Definitions.Def_BirthdayEntropy_Soundness_Counting

noncomputable section
open scoped Classical

namespace BirthdayEntropy.Soundness

/-- Lemma 4.2, PDF p7 / printed p6, both formulations. Only occupied
cells are read, avoiding meaningless logarithms of empty-cell upper bounds. -/
theorem entropy_cell_counting {α τ : Type*} [Fintype α] [Fintype τ]
    (Ω : Finset α) (hΩ : Ω.Nonempty) (F : α → τ) (Mcell : τ → ℝ)
    (hcell : ∀ f, (cell Ω F f).Nonempty → ((cell Ω F f).card : ℝ) ≤ Mcell f) :
    let Q := uniformOn Ω hΩ
    Real.log (Ω.card : ℝ) ≤ (Q.map F).entropy + Q.mean (fun a => Real.log (Mcell (F a))) ∧
    ∀ (M : ℝ) (s : τ → ℝ),
      (∀ f, (cell Ω F f).Nonempty → Mcell f ≤ M * Real.exp (-s f)) →
      Q.mean (fun a => s (F a)) - (Q.map F).entropy ≤ Real.log (M / Ω.card) := by sorry

end BirthdayEntropy.Soundness
