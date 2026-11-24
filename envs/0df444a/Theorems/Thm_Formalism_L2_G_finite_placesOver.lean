-- Prove2me | Theorems.Thm_Formalism_L2_G_finite_placesOver
-- name    : Formalism.L2.G.finite_placesOver
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:53.183799+00:00
-- url     : https://prove2.me/theorems/d0ab7aed-1d82-4032-99cd-86742332ae0c
-- title:
--   G: finite places Over
-- statement:
--   The G construction uses the finite places Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/LevelCharts/AtGGlob.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/LevelCharts/AtGGlob.lean#L14-L21

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_LevelCharts_SignBlockDeterminant
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_LevelCharts_AtGGlob
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.G
variable (F : Type) [Field F] [NumberField F]

theorem Formalism.L2.G.finite_placesOver (g : ℕ) (hg : g ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | ((g : ℕ) : 𝓞 F) ∈ v.asIdeal}.Finite := by sorry
