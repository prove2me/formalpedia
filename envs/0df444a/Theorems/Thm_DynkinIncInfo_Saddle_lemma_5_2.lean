-- Prove2me | Theorems.Thm_DynkinIncInfo_Saddle_lemma_5_2
-- name    : DynkinIncInfo.Saddle.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:56.509985+00:00
-- url     : https://prove2.me/theorems/3e1fa2a7-4d36-427e-b352-7692dac10d98
-- title:
--   Lemma 5.2, p. 14 — S'2 is left-connected and S'1 right-connected in z (k ≠ 0)
-- statement:
--   Assume $k\neq0$. Let $(z_0,y_0)\in R_K$. Then:
--
--   1. if $(z_0,y_0)\in\mathcal S'_2$, then $(z,y_0)\in\mathcal S'_2$ for every $z\le z_0$ with $(z,y_0)\in R_K$;
--   2. if $(z_0,y_0)\in\mathcal S'_1$, then $(z,y_0)\in\mathcal S'_1$ for every $z\ge z_0$.
--
--   The stopping regions in parabolic coordinates are connected in the time-like variable $z$.
--
--   **Formalization Note.** $k\neq0$ is the standing assumption of §5 ("In the rest of the paper we study the case $k\neq0$", p. 12).
-- source:
--   De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 14, Lemma 5.2

import Mathlib
import Definitions.Def_DynkinIncInfo_Saddle_Model
import Definitions.Def_DynkinIncInfo_Saddle_Game
import Definitions.Def_DynkinIncInfo_Saddle_Regions

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinIncInfo.Saddle

/-- De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 14, Lemma 5.2: let `(z0, y0) ∈ R_K`.
(i) `(z0, y0) ∈ 𝒮'2 ⟹ (z, y0) ∈ 𝒮'2` for all `z ≤ z0` such that `(z, y0) ∈ R_K`;
(ii) `(z0, y0) ∈ 𝒮'1 ⟹ (z, y0) ∈ 𝒮'1` for all `z ≥ z0`.

**Formalization Note.** The hypothesis `k ≠ 0` is §5's standing assumption ("In the rest of the
paper we study the case `k ≠ 0`", p. 12). Model conventions: the paper's `(X, Y)` (solution of the SDE (2.3)) is represented on the original space of §2 by `X := S` (2.1) and the closed-form Bayes filter `Y`, which have the same law (p. 6); `D^y = 1{U < y}` with `U` uniform and independent of `B`; stopping times are `𝓕̄^S`-stopping times (the filtration of `S` augmented by the null sets) valued in `[0, ∞]`; `M` is a `lintegral` with payoff `0` on `{τ ∧ γ = ∞}`; `V := V̄.toReal`. -/
theorem lemma_5_2 {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (hk : k p ≠ 0) (z0 y0 : ℝ) (h0 : (z0, y0) ∈ RK p) :
    ((z0, y0) ∈ S2' p st → ∀ z : ℝ, z ≤ z0 → (z, y0) ∈ RK p → (z, y0) ∈ S2' p st) ∧
    ((z0, y0) ∈ S1' p st → ∀ z : ℝ, z0 ≤ z → (z, y0) ∈ S1' p st) := by sorry

end DynkinIncInfo.Saddle
