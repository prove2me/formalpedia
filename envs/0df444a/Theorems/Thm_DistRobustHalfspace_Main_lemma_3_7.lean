-- Prove2me | Theorems.Thm_DistRobustHalfspace_Main_lemma_3_7
-- name    : DistRobustHalfspace.Main.lemma_3_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:18:25.796209+00:00
-- url     : https://prove2.me/theorems/c9a19b92-67ef-41d5-a290-78d82d05c071
-- title:
--   Lemma 3.7 — F_ε = trunc_{±R_ε}∘Φ⁻¹ is absolutely continuous with ‖F′_ε‖_∞ ≤ C/ε^{25/2}
-- statement:
--   There is an absolute constant $C$ such that, for every $\varepsilon\in(0,\varepsilon_0]$ (standing assumption), the function $F_\varepsilon=\operatorname{trunc}_{\pm R_\varepsilon}\circ\Phi^{-1}:[0,1]\to\mathbb R$ is absolutely continuous and
--   $$\|F_\varepsilon'\|_\infty\ \le\ C/\varepsilon^{25/2}.$$
--   Here $\Phi^{-1}(0)=-\infty$ and $\Phi^{-1}(1)=+\infty$, so $F_\varepsilon(0)=-R_\varepsilon$ and $F_\varepsilon(1)=R_\varepsilon$.
--
--   Differences from the source:
--   - encoding: standing assumptions n ≥ n₀, ε ≤ ε₀, ε ≥ 1/n; C an absolute constant → `∃ C > 0, ∃ ε₀ > 0, ∀ ε ∈ (0, ε₀]`; reason: the statement does not involve n, so the n-conditions change nothing
--   - encoding: F_ε : [0, 1] → ℝ absolutely continuous, ‖F′_ε‖_∞ ≤ C/ε^{25/2} → `AbsolutelyContinuousOnInterval (Feps ε) 0 1` and `|deriv (Feps ε) q| ≤ C/ε^{25/2}` for Lebesgue-a.e. q ∈ [0, 1]; reason: the essential supremum of the a.e.-defined derivative of an absolutely continuous function
--   - encoding: Φ⁻¹ extended by ∓∞ at 0, 1 → published `Cohen2019.Robust.PhiInv` (EReal); reason: the same extension (Definition 2.12)
-- source:
--   Xi Chen, Renato Ferreira Pinto Jr., Nathaniel Harms, Rocco A. Servedio, Distribution-Robust Halfspace Testing, 2026 (STOC 2027 submission manuscript, sha256 545c331d…1018a87), Lemma 3.7, p. 28 (PDF 30)

import Mathlib
import Definitions.Def_DistRobustHalfspace_Main_Testers
import Definitions.Def_DistRobustHalfspace_Main_Estimators
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace DistRobustHalfspace.Main

/-- Lemma 3.7 (p. 28): `F_ε = trunc_{±R_ε} ∘ Φ⁻¹ : [0, 1] → ℝ` is absolutely continuous and
`‖F_ε′‖_∞ ≤ C / ε^{25/2}` for an absolute constant `C` (for `ε ≤ ε₀`, the standing assumption). -/
theorem lemma_3_7 :
    ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      AbsolutelyContinuousOnInterval (Feps ε) 0 1 ∧
      ∀ᵐ q ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        |deriv (Feps ε) q| ≤ C / ε ^ ((25 : ℝ) / 2) := by sorry

end DistRobustHalfspace.Main
