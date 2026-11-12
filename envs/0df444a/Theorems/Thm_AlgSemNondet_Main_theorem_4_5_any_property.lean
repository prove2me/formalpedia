-- Prove2me | Theorems.Thm_AlgSemNondet_Main_theorem_4_5_any_property
-- name    : AlgSemNondet.Main.theorem_4_5_any_property
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:49:41.959206+00:00
-- url     : https://prove2.me/theorems/ab438724-98b3-41a5-80a6-e31a3e5f0694
-- title:
--   Theorem 4.5 for every property and two data symbols (strengthened: intrinsicness and the fourth data symbol dropped)
-- statement:
--   **Source** (Theorem 4.5, p. 17): if $\Gamma$ contains the blank $B$ and at least four data symbols, and $\mathfrak{P}$ is an intrinsic property, then for the machine $M$ there exist an algebraic encoding $\varepsilon$ and an input $w \in (\Gamma \setminus \{B\})^+$ with $\mathfrak{P}(M, w)$ not equivalent to "$M$ associates $\varepsilon$-incommensurable elements on $w$".
--
--   **Variant:** the same conclusion for every property $\mathfrak{P}$, intrinsic or not, as soon as $\Gamma$ has at least two symbols different from $B$.
--
--   **Difference:** the intrinsic hypothesis is removed and four data symbols are weakened to two; the conclusion and its quantifier order are unchanged.
-- source:
--   Zheng, Zheng, Wang and Huang, An Algebraic Semantic Framework for Nondeterministic Computation, July 2026, Theorem 4.5, p.17 (strengthened)

import Mathlib
import Definitions.Def_AlgSemNondet_Main_TuringMachine
import Definitions.Def_AlgSemNondet_Main_AlgebraicEncoding

theorem AlgSemNondet.Main.theorem_4_5_any_property {Q Γ : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype Γ] [DecidableEq Γ] {B : Γ} (hΓ : 2 ≤ Fintype.card {c : Γ // c ≠ B})
    (M : AlgSemNondet.Main.TuringMachine Q Γ B)
    (P : AlgSemNondet.Main.TuringMachine Q Γ B → List Γ → Prop) :
    ∃ (ε : AlgSemNondet.Main.AlgebraicEncoding Γ B) (w : List Γ), w ≠ [] ∧ (∀ c ∈ w, c ≠ B) ∧
      ¬ (P M w ↔ ε.AssociatesIncommensurable w) := by sorry
