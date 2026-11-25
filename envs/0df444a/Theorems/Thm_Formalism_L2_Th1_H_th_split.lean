-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_th_split
-- name    : Formalism.L2.Th1.H.th_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:47.720485+00:00
-- url     : https://prove2.me/theorems/3440c7e4-d231-4b21-81fc-d1c5d383d829
-- title:
--   H: th split
-- statement:
--   The H construction uses the th split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/Th0CharMulOpUTh0HalfPeriodEq.lean#L214-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/Th0CharMulOpUTh0HalfPeriodEq.lean#L214-L280

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstIsogeny
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Th0TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H

theorem Formalism.L2.Th1.H.th_split (L : PeriodPair) (ω₀ : ℂ) (n : Type) [Fintype n] [DecidableEq n] (h0 : ω₀ ∈ L.lattice)
    (hh : ω₀ / 2 ∉ L.lattice) (α : (n → ℂ) → ℂ) (hα : ∀ x ∈ stdLat L n, α x = stdChar L ω₀ x)
    (G : (n → ℂ) → ℂ) (hG : G ∈ Th (stdH L n) α (stdLat L n)) (w : n → ℂ) (i : n) :
    G w = G (Function.update w i 0) * Formalism.L2.Th1.F.th0 L (ω₀ / 2) (w i) := by sorry
