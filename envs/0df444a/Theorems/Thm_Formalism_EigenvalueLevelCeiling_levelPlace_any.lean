-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_levelPlace_any
-- name    : Formalism.EigenvalueLevelCeiling.levelPlace_any
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:11.449366+00:00
-- url     : https://prove2.me/theorems/3bee3b13-2962-4828-a540-205e45096962
-- title:
--   Eigenvalue Level Ceiling: level Place any
-- statement:
--   The Eigenvalue Level Ceiling construction uses the level Place any property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/GlobalBoundRefinements.lean#L524-L532
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/GlobalBoundRefinements.lean#L524-L532

import Definitions.Def_Formalism_MirabolicMackeyTheory_LocalConditionsWeighted
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues

theorem Formalism.EigenvalueLevelCeiling.levelPlace_any (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K))
    (nnL nnF q Z1 Z2 : K) (T c : ℕ) (E : ℤ) (h1 : nnL ≠ 0) (h2 : nnF ≠ 0) (h3 : q ≠ 0) (h4 : Z1 ≠ 0) (h5 : Z2 ≠ 0)
    (z1 : vw w Z1 = 0) (z2 : vw w Z2 = 0) (hq : 0 ≤ vw w q) (hT : 1 ≤ T) (hE : E ≤ ramw w * ((T : ℤ) + 1)) :
    E - vw w ((nnL * Z1) ^ T * (nnF * q ^ c * Z2)) ≤ ramw w * (2 * (T : ℤ)) - vw w (nnL ^ T * nnF) := by sorry
