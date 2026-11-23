-- Prove2me | Theorems.Thm_Formalism_ELL_PadicLogarithmSubstitution_norm_finsum_le_one
-- name    : Formalism.ELL.PadicLogarithmSubstitution.norm_finsum_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:19:04.985369+00:00
-- url     : https://prove2.me/theorems/9b1ed0a9-f95f-4e02-9c7b-aa0fd62ef5b1
-- title:
--   Padic Logarithm Substitution: norm finsum le one
-- statement:
--   The Padic Logarithm Substitution construction uses the norm finsum le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IntegralPSBserSubOne.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IntegralPSBserSubOne.lean#L36-L40

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_IntegralPSBserSubOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.PadicLogarithmSubstitution
open Formalism.G Formalism.ELL
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem Formalism.ELL.PadicLogarithmSubstitution.norm_finsum_le_one {f : ℕ → K} (h : ∀ n, ‖f n‖ ≤ 1) : ‖∑ᶠ n, f n‖ ≤ 1 := by sorry
