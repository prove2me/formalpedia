-- Prove2me | Theorems.Thm_EuclidCVRP_Main_lemma_6
-- name    : EuclidCVRP.Main.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:16.615838+00:00
-- url     : https://prove2.me/theorems/4e8cc52e-4460-43f3-8ee1-a1e4d81c3447
-- title:
--   Lemma 6 — a slack solution of cost 1.5 + O(ε)
-- statement:
--   Work in the setting of Section 2 and let $\eta_{\mathrm{slack}}=\min\{\varepsilon/D,1/K\}$. There are an absolute constant $C>0$ and an absolute $\varepsilon_0>0$ such that for every $\varepsilon\in(0,\varepsilon_0)$, $D\ge1$ and $\Gamma$ there is a bound $B$ (depending only on $\varepsilon,D,\Gamma$) with the following property. For every instance and $\mathrm{OPT}$ in the setting there is a feasible solution $\mathrm{OPT}'$ with $|\mathrm{OPT}'|\le B$ and an injective correspondence $T\mapsto T'$ from $\mathrm{OPT}$ to $\mathrm{OPT}'$ such that
--
--   1. $V_{\mathrm{fixed}}(T)\subseteq V(T')$ for every $T\in\mathrm{OPT}$;
--   2. $d(V(T')\setminus V_{\mathrm{fixed}}(T))\le(1-\eta_{\mathrm{slack}})\,Q_T$ for every $T\in\mathrm{OPT}$;
--   3. every tour of $\mathrm{OPT}'$ that does not correspond to a tour of $\mathrm{OPT}$ has total demand at most $(1-\eta_{\mathrm{slack}})Q$;
--   4. the cost satisfies
--   $$c(\mathrm{OPT}')\le\Bigl(\tfrac32+C\varepsilon\Bigr)\,c(\mathrm{OPT}).$$
--
--   The slack created here is what makes the rounded dynamic program of Theorem 4 feasible.
--
--   Differences from the source:
--   - reading: O(ε), with ε > 0 ("throughout, we may assume that ε > 0 is sufficiently small, in particular ε < 1/2", p. 6) → an absolute constant C > 0 quantified before ε, D, Γ and the instance, and the claim for all ε ∈ (0, ε₀) for an absolute ε₀ > 0; reason: the paper's standing convention on ε; C never depends on D, since Theorem 1 takes D = D_ε
--   - encoding: Section 2: a D-bounded instance and an optimum OPT with |OPT| ≤ Γ → Sec2.Setting: valid D-bounded instance, OPT optimal, at most Γ tours, all nonempty; D ≥ 1; reason: the tours of |OPT| are nonempty (a tour without clients is not counted); D ≥ 1 is implied by D-boundedness when n ≥ 1
--   - reading: a sufficiently fine square grid of cells of side τ = ε²/D partitioning the annulus; "the exact construction of the cells is not important" (p. 7) → the grid of half-open squares [a, a+τ) × [b, b+τ) with the depot at a grid vertex; K = (2⌈D/τ⌉+1)² cells cover the disc of radius D; reason: half-open cells partition the plane, so every client lies in exactly one cell; K depends only on ε and D
--   - reading: for every tour T ∈ OPT there is a corresponding tour T′ ∈ OPT′ → an injective map from the tours of OPT to the tours of OPT′; reason: the proof of Theorem 4 assigns each T′ the leftover capacity Q_T of the unique T it corresponds to
--   - encoding: |OPT′| = O_ε(1) → |OPT′| ≤ B with B quantified after ε, D, Γ and before the instance; reason: O_ε(1) with D, Γ = O_ε(1)
-- source:
--   Jannis Blauth, Fabrizio Grandoni, Bence Mátravölgyi, Ramin Mousavi, Kinter Ren, Mohammad R. Salavatipour, STOC 2027 submission #1236 (October 2026), p. 7, Lemma 6

import Mathlib
import Definitions.Def_EuclidCVRP_Main_Section2

set_option autoImplicit false

namespace EuclidCVRP.Main

open Sec2

/-- **Lemma 6** (p. 7). In the setting of Section 2, with `η_slack = min{ε/D, 1/K}`, there is a feasible
solution `OPT'` with `|OPT'| = O_ε(1)` (a bound `B` depending only on `ε`, `D`, `Γ`) and an injective
correspondence `T ↦ T'` from `OPT` to `OPT'` such that `V_fixed(T) ⊆ V(T')`,
`d(V(T') \ V_fixed(T)) ≤ (1 − η_slack) Q_T`, every tour of `OPT'` not corresponding to a tour of
`OPT` has demand at most `(1 − η_slack) Q`, and `c(OPT') ≤ (1.5 + O(ε)) c(OPT)`, the `O(ε)` an
absolute constant. -/
theorem lemma_6 :
    ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ D : ℝ, 1 ≤ D → ∀ Γ : ℕ, ∃ B : ℕ,
        ∀ (I : Instance) (OPT : List (List (Fin I.n))), Setting I D OPT Γ →
        ∃ OPT' : List (List (Fin I.n)), I.Feasible OPT' ∧ OPT'.length ≤ B ∧
          ∃ f : Fin OPT.length → Fin OPT'.length, Function.Injective f ∧
            (∀ j, Vfixed I ε D OPT j ⊆ (OPT'[f j]).toFinset) ∧
            (∀ j, (I.demSet ((OPT'[f j]).toFinset \ Vfixed I ε D OPT j) : ℝ) ≤
              (1 - ηslack ε D) * QT I ε D OPT j) ∧
            (∀ k, k ∉ Set.range f → (I.tourDem OPT'[k] : ℝ) ≤ (1 - ηslack ε D) * I.Q) ∧
            I.cost OPT' ≤ (3 / 2 + C * ε) * I.cost OPT := by sorry

end EuclidCVRP.Main
