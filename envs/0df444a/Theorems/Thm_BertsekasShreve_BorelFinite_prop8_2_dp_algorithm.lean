-- Prove2me | Theorems.Thm_BertsekasShreve_BorelFinite_prop8_2_dp_algorithm
-- name    : BertsekasShreve.BorelFinite.prop8_2_dp_algorithm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:18:24.105641+00:00
-- url     : https://prove2.me/theorems/fcd480fc-ab15-459d-a962-d17055263e14
-- title:
--   Proposition 8.2 — the DP algorithm gives the optimal cost over all universally measurable policies: J*_K = T^K(J₀)
-- statement:
--   Consider the finite horizon Borel model of Definition 8.1 and assume (F⁺) or (F⁻). Let $J_0$ be the identically zero function on $S$. Then
--   $$J^*_K=T^K(J_0),\qquad K=1,\dots,N.$$
--
--   Here $J^*_K(x)=\inf_{\pi\in\Pi'}J_{K,\pi}(x)$ is the infimum of the $K$-stage cost over all policies — history-dependent, randomized, with universally measurable kernels — and $J_{K,\pi}$ is the expected discounted cost of Definition 8.3, defined through the measure $r_N(\pi,p_x)$. The dynamic programming algorithm, which starts from the zero function and applies $T$ repeatedly, therefore computes the optimal cost of the finite horizon Borel model.
--
--   **Formalization Note** "(F⁺) or (F⁻)" is the hypothesis `FPlus M ∨ FMinus M`. The cost $J_{K,\pi}$ is the integral of the stage sum, not the operator composition of Lemma 8.1, and the infimum ranges over all policies, not only Markov ones.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 198, Proposition 8.2 (Eq. (18) of Chapter 8)

import Mathlib
import Definitions.Def_BertsekasShreve_BorelFinite_Model
import Definitions.Def_BertsekasShreve_BorelFinite_Policy
import Definitions.Def_BertsekasShreve_BorelFinite_Operators

namespace BertsekasShreve.BorelFinite

/-- **Proposition 8.2** (p. 198). Under (F⁺) or (F⁻), with `J₀` the identically zero function on
`S`, `J*_K = T^K(J₀)` for `K = 1, …, N` (Eq. (18) of Chapter 8). Here `J*_K` is the infimum of the
`K`-stage cost over all (history-dependent, randomized, universally measurable) policies. -/
theorem prop8_2_dp_algorithm {S C W : Type*}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [Nonempty S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [Nonempty C]
    [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [Nonempty W]
    (M : Model S C W)
    (hF : FPlus M ∨ FMinus M) (K : ℕ) (hK1 : 1 ≤ K) (hKN : K ≤ M.N) :
    Jstar M K = (T M)^[K] (J0 S) := by sorry

end BertsekasShreve.BorelFinite
