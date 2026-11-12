-- Prove2me | Theorems.Thm_EuclidCVRP_Main_lemma_7
-- name    : EuclidCVRP.Main.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:06.98527+00:00
-- url     : https://prove2.me/theorems/4db77d8b-52d4-4a8d-ab39-b4dc85e002d0
-- title:
--   Lemma 7 — a short walk through all dense cells
-- statement:
--   Work in the setting of Section 2, with an admissible dense cell $\mathrm{Cell}(T)$ for every tour $T\in\mathrm{OPT}$ with $d(V_{\mathrm{left}}(T))>0$. There is an absolute constant $C>0$ (and an absolute $\varepsilon_0>0$) such that for every $\varepsilon\in(0,\varepsilon_0)$ there is a closed walk $P$ through the depot with
--
--   1. $P$ traverses $\mathrm{Cell}(T)$ for every tour $T\in\mathrm{OPT}$ with $d(V_{\mathrm{left}}(T))>0$;
--   2. its length satisfies
--   $$c(P)\le\Bigl(\tfrac12+C\varepsilon\Bigr)\,c(\mathrm{OPT}).$$
--
--   The walk $P$ is the starting point of Lemma 9.
--
--   **Formalization Note** The proof gives $c(P)\le(\tfrac12+\tau/\sqrt2)\,c(\mathrm{OPT})$ with $\tau=\varepsilon^2/D\le\varepsilon$; the statement keeps the source's $O(\varepsilon)$ as an absolute constant.
--
--   Differences from the source:
--   - reading: O(ε), with ε > 0 ("throughout, we may assume that ε > 0 is sufficiently small, in particular ε < 1/2", p. 6) → an absolute constant C > 0 quantified before ε, D, Γ and the instance, and the claim for all ε ∈ (0, ε₀) for an absolute ε₀ > 0; reason: the paper's standing convention on ε; C never depends on D, since Theorem 1 takes D = D_ε
--   - encoding: Section 2: a D-bounded instance and an optimum OPT with |OPT| ≤ Γ → Sec2.Setting: valid D-bounded instance, OPT optimal, at most Γ tours, all nonempty; D ≥ 1; reason: the tours of |OPT| are nonempty (a tour without clients is not counted); D ≥ 1 is implied by D-boundedness when n ≥ 1
--   - reading: a sufficiently fine square grid of cells of side τ = ε²/D partitioning the annulus; "the exact construction of the cells is not important" (p. 7) → the grid of half-open squares [a, a+τ) × [b, b+τ) with the depot at a grid vertex; K = (2⌈D/τ⌉+1)² cells cover the disc of radius D; reason: half-open cells partition the plane, so every client lies in exactly one cell; K depends only on ε and D
--   - generalization: "Fix one such cell and denote it by Cell(T)" (p. 8) → every choice of an admissible dense cell Cell(T) for each tour with d(V_left(T)) > 0; reason: holding for every choice specializes to the fixed one
--   - encoding: closed walk P containing r → a list of points of the plane containing the depot, with its closed polygonal length; reason: the walk is the closed polygon through its points
-- source:
--   Jannis Blauth, Fabrizio Grandoni, Bence Mátravölgyi, Ramin Mousavi, Kinter Ren, Mohammad R. Salavatipour, STOC 2027 submission #1236 (October 2026), p. 8, Lemma 7

import Mathlib
import Definitions.Def_EuclidCVRP_Main_Section2

set_option autoImplicit false

namespace EuclidCVRP.Main

open Sec2

/-- **Lemma 7** (p. 8). In the setting of Section 2, with an admissible dense cell `Cell(T)` for every
tour `T ∈ OPT` with `d(V_left(T)) > 0`, there is a closed walk `P` through the depot traversing every
such `Cell(T)` with `c(P) ≤ (1/2 + O(ε)) c(OPT)`; the `O(ε)` is an absolute constant `C`. -/
theorem lemma_7 :
    ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ D : ℝ, 1 ≤ D → ∀ (Γ : ℕ) (I : Instance)
        (OPT : List (List (Fin I.n))), Setting I D OPT Γ →
        ∀ cell : Fin OPT.length → ℤ × ℤ,
          (∀ j, 0 < I.demSet (Vleft I ε D OPT j) → IsDenseCell I ε D OPT j (cell j)) →
          ∃ P : List Pt, I.depot ∈ P ∧
            (∀ j, 0 < I.demSet (Vleft I ε D OPT j) → Traverses P (cellSet I ε D (cell j))) ∧
            closedLen P ≤ (1 / 2 + C * ε) * I.cost OPT := by sorry

end EuclidCVRP.Main
