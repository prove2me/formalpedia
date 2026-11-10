-- Prove2me | Theorems.Thm_DistRobustHalfspace_Main_lemma_2_2
-- name    : DistRobustHalfspace.Main.lemma_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:18:24.268193+00:00
-- url     : https://prove2.me/theorems/bb632523-c9ae-40a4-b760-e5bb138a1d4c
-- title:
--   Lemma 2.2 — τ(t̂) ≥ √(2/π)·ε² when |t̂| ≤ T_ε
-- statement:
--   For every $\varepsilon\in(0,\varepsilon_0]$ (the standing assumption of §2.1) and every $\hat t\in\mathbb R$ with $|\hat t|\le T_\varepsilon=2\sqrt{\log(1/\varepsilon)}$,
--   $$\tau(\hat t)\ \ge\ \sqrt{2/\pi}\cdot\varepsilon^2,$$
--   where $\tau(t)=\mathbb E_{g\sim\mathcal N(0,1)}[g\operatorname{sign}(g-t)]$.
--
--   Differences from the source:
--   - encoding: standing assumptions n ≥ n₀, ε ≤ ε₀, ε ≥ 1/n (p. 11) → `∃ ε₀ > 0, ∀ ε ∈ (0, ε₀]`; reason: the statement does not involve n, and for every ε > 0 some n ≥ n₀ has 1/n ≤ ε, so the n-conditions change nothing
--   - reading: sign(⟨w, x⟩ − t) with sign(0) unspecified → `sgn 0 = 1` (sign(0) = +1); reason: the paper never fixes sign(0); a {±1}-valued sign needs a value there
-- source:
--   Xi Chen, Renato Ferreira Pinto Jr., Nathaniel Harms, Rocco A. Servedio, Distribution-Robust Halfspace Testing, 2026 (STOC 2027 submission manuscript, sha256 545c331d…1018a87), Lemma 2.2, p. 12 (PDF 14)

import Mathlib
import Definitions.Def_DistRobustHalfspace_Main_Testers
import Definitions.Def_DistRobustHalfspace_Main_Estimators
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace DistRobustHalfspace.Main

/-- Lemma 2.2 (p. 12): if `|t̂| ≤ T_ε` then `τ(t̂) ≥ √(2/π) · ε²` (for `ε ≤ ε₀`, the standing
assumption of Sections 2–3). -/
theorem lemma_2_2 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ t : ℝ, |t| ≤ Teps ε →
      Real.sqrt (2 / Real.pi) * ε ^ 2 ≤ tau t := by sorry

end DistRobustHalfspace.Main
