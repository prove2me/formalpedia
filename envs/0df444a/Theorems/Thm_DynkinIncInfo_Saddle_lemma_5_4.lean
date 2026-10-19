-- Prove2me | Theorems.Thm_DynkinIncInfo_Saddle_lemma_5_4
-- name    : DynkinIncInfo.Saddle.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:13.128645+00:00
-- url     : https://prove2.me/theorems/9a5847fa-54ef-405c-a66b-f73ef80ebbc5
-- title:
--   Lemma 5.4, p. 14 — under σ²/δ0 ≥ 1, S'2 is up-connected and S'1 down-connected in y; v decreasing above yK
-- statement:
--   Assume $\sigma^2/\delta_0\ge1$ (Assumption 5.3) and $k\neq0$. Then for every $(z_0,y_0)\in R_K$:
--
--   1. if $(z_0,y_0)\in\mathcal S'_2$, then $(z_0,y)\in\mathcal S'_2$ for every $y\ge y_0$ with $(z_0,y)\in R_K$;
--   2. if $(z_0,y_0)\in\mathcal S'_1$, then $(z_0,y)\in\mathcal S'_1$ for every $y\in(0,y_0]$.
--
--   Moreover,
--
--   3. $v(z,y')\le v(z,y)$ whenever $y_K(z)<y\le y'<1$, $z\in\mathbb R$.
--
--   These connectedness properties in $y$ are what make the boundary $c_1$ of $\mathcal S'_1$ a function.
--
--   **Formalization Note.** In (2) the range $y>0$ and in (3) the bound $y'<1$ come from $\mathcal S'_1\subseteq\mathbb R\times(0,1)$ and the domain of $v$. $k\neq0$ is the standing assumption of §5.
-- source:
--   De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 14, Lemma 5.4 (with Assumption 5.3)

import Mathlib
import Definitions.Def_DynkinIncInfo_Saddle_Model
import Definitions.Def_DynkinIncInfo_Saddle_Game
import Definitions.Def_DynkinIncInfo_Saddle_Regions

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinIncInfo.Saddle

/-- De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 14, Lemma 5.4 (under Assumption 5.3, `σ²/δ0 ≥ 1`): let `(z0, y0) ∈ R_K`; then
(i) `(z0, y0) ∈ 𝒮'2 ⟹ (z0, y) ∈ 𝒮'2` for all `y ≥ y0` such that `(z0, y) ∈ R_K`;
(ii) `(z0, y0) ∈ 𝒮'1 ⟹ (z0, y) ∈ 𝒮'1` for all `y ≤ y0`.
Moreover (iii) `v(z, y') ≤ v(z, y)` for `y' ≥ y > y_K(z)`, `z ∈ ℝ`.

**Formalization Note.** In (ii) `y` ranges over `(0, y0]` (`𝒮'1 ⊆ ℝ × (0, 1)`); in (iii) `y' < 1`
(`v` is defined on `ℝ × (0, 1)`). `k ≠ 0` is §5's standing assumption (p. 12). Model
conventions: the paper's `(X, Y)` (solution of the SDE (2.3)) is represented on the original space of §2 by `X := S` (2.1) and the closed-form Bayes filter `Y`, which have the same law (p. 6); `D^y = 1{U < y}` with `U` uniform and independent of `B`; stopping times are `𝓕̄^S`-stopping times (the filtration of `S` augmented by the null sets) valued in `[0, ∞]`; `M` is a `lintegral` with payoff `0` on `{τ ∧ γ = ∞}`; `V := V̄.toReal`. -/
theorem lemma_5_4 {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (h53 : 1 ≤ p.σ ^ 2 / p.δ0) (hk : k p ≠ 0) :
    (∀ z0 y0 : ℝ, (z0, y0) ∈ RK p →
      ((z0, y0) ∈ S2' p st → ∀ y : ℝ, y0 ≤ y → (z0, y) ∈ RK p → (z0, y) ∈ S2' p st) ∧
      ((z0, y0) ∈ S1' p st → ∀ y : ℝ, 0 < y → y ≤ y0 → (z0, y) ∈ S1' p st)) ∧
    (∀ z y y' : ℝ, yK p z < y → y ≤ y' → y' < 1 → v p st z y' ≤ v p st z y) := by sorry

end DynkinIncInfo.Saddle
