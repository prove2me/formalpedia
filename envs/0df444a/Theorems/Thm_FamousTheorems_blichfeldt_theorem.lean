-- Prove2me | Theorems.Thm_FamousTheorems_blichfeldt_theorem
-- name    : FamousTheorems.blichfeldt_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:04:31.476714+00:00
-- url     : https://prove2.me/theorems/a08c45c2-9247-4c73-a39e-1c0f9dc2bb56
-- title:
--   Blichfeldt's theorem
-- statement:
--   **Blichfeldt's theorem.** Let a countable group $L$ act measurably on a measure space $(E,\mu)$ preserving $\mu$, and let $F$ be a fundamental domain for the action. If a null-measurable set $s$ satisfies $\mu(s)>\mu(F)$, then two distinct translates of $s$ overlap: there are $x\ne y$ in $L$ with $(x+s)\cap(y+s)\ne\varnothing$.
--
--   For a lattice $L\subset\mathbb R^n$ acting by translation, this says that a set of volume larger than the covolume of $L$ contains two points whose difference lies in $L$. It is the pigeonhole principle of the geometry of numbers. Minkowski's convex body theorem, the basic tool for finiteness of class groups and Dirichlet's unit theorem, follows from it.
--
--   **Formalization note.** Mathlib's `MeasureTheory.exists_pair_mem_lattice_not_disjoint_vadd`. `IsAddFundamentalDomain L F μ` means the translates of `F` cover `E` up to a null set and are a.e. disjoint. `VAddInvariantMeasure L E μ` means the action preserves `μ`, and `x +ᵥ s` is the translate of `s` by `x`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.exists_pair_mem_lattice_not_disjoint_vadd`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory Pointwise

theorem blichfeldt_theorem {E L : Type*} [MeasurableSpace E] {μ : Measure E} {F s : Set E} [AddGroup L] [Countable L]
    [AddAction L E] [MeasurableSpace L] [MeasurableVAdd L E] [VAddInvariantMeasure L E μ]
    (fund : IsAddFundamentalDomain L F μ) (hS : NullMeasurableSet s μ) (h : μ F < μ s) :
    ∃ x y : L, x ≠ y ∧ ¬Disjoint (x +ᵥ s) (y +ᵥ s) := by sorry

end FamousTheorems
