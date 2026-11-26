-- Prove2me | Theorems.Thm_Eden_eventually_dimension_formula_of_neutral_prefix
-- name    : Eden.eventually_dimension_formula_of_neutral_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:58:32.361797+00:00
-- url     : https://prove2.me/theorems/c412319c-97ed-4b02-b298-f2a22a2573a4
-- title:
--   Eden: eventually dimension formula of neutral prefix
-- statement:
--   The Eden construction uses the eventually dimension formula of neutral prefix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/EventualDimensionFormulas.lean#L133-L171
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/EventualDimensionFormulas.lean#L133-L171

import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_EventualDimensionFormulas
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.eventually_dimension_formula_of_neutral_prefix (c : ℝ) (p : PhaseSpace)
    {k : ℕ} (hk : k < 5)
    (hlim₀ : ∀ i : Fin 5, i.val < k → lyapunovExponent c p i = 0)
    (hlim₁ : lyapunovExponent c p ⟨k, hk⟩ < 0)
    (hfinite : ∀ᶠ t in atTop, ∀ i : Fin 5, i.val < k →
      0 ≤ normalizedLogSingularValues c t p i) :
    ∀ᶠ t in atTop,
      (∀ i : Fin 5, i.val < k → 0 ≤ normalizedLogSingularValues c t p i) ∧
      spectrumPartialSum (normalizedLogSingularValues c t p) (k + 1) < 0 ∧
      normalizedLogSingularValues c t p ⟨k, hk⟩ < 0 ∧
      finiteTimeDimension c t p = (k : ℝ) +
        spectrumPartialSum (normalizedLogSingularValues c t p) k /
          -normalizedLogSingularValues c t p ⟨k, hk⟩ := by sorry
