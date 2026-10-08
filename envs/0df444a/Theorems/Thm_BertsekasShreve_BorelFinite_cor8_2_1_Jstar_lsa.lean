-- Prove2me | Theorems.Thm_BertsekasShreve_BorelFinite_cor8_2_1_Jstar_lsa
-- name    : BertsekasShreve.BorelFinite.cor8_2_1_Jstar_lsa
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:56:37.862759+00:00
-- url     : https://prove2.me/theorems/16db6f13-8843-4391-b4eb-6d03e1d1c27b
-- title:
--   Corollary 8.2.1 — the K-stage optimal cost J*_K is lower semianalytic
-- statement:
--   Consider the finite horizon Borel model of Definition 8.1 and assume (F⁺) or (F⁻). For $K=1,2,\dots,N$ the function
--   $$J^*_K:S\to R^*$$
--   is lower semianalytic: $\{x\in S\mid J^*_K(x)<c\}$ is analytic for every real $c$.
--
--   The optimal cost need not be Borel-measurable even when $\Gamma=S\times C$ and $g$ is Borel (Example 1 of Chapter 8); lower semianalyticity is the regularity that survives.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 200, Corollary 8.2.1

import Mathlib
import Definitions.Def_BertsekasShreve_BorelFinite_Model
import Definitions.Def_BertsekasShreve_BorelFinite_Policy

namespace BertsekasShreve.BorelFinite

/-- **Corollary 8.2.1** (p. 200). Under (F⁺) or (F⁻), for `K = 1, …, N` the function `J*_K` is
lower semianalytic. -/
theorem cor8_2_1_Jstar_lsa {S C W : Type*}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [Nonempty S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [Nonempty C]
    [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [Nonempty W]
    (M : Model S C W)
    (hF : FPlus M ∨ FMinus M) (K : ℕ) (hK1 : 1 ≤ K) (hKN : K ≤ M.N) :
    IsLowerSemianalyticOn Set.univ (Jstar M K) := by sorry

end BertsekasShreve.BorelFinite
