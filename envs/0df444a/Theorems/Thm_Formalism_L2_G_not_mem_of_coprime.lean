-- Prove2me | Theorems.Thm_Formalism_L2_G_not_mem_of_coprime
-- name    : Formalism.L2.G.not_mem_of_coprime
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:23:34.516797+00:00
-- url     : https://prove2.me/theorems/2db11241-477b-4e17-ae1a-8e3a89fd4103
-- title:
--   G: not mem of coprime
-- statement:
--   The G construction uses the not mem of coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/LevelCharts/AtGLev.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/LevelCharts/AtGLev.lean#L12-L20

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_LevelCharts_AtGGlob
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_LevelCharts_AtGLev
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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

theorem Formalism.L2.G.not_mem_of_coprime {p g : ℕ} (h : Nat.Coprime p g) (v : HeightOneSpectrum (𝓞 F))
    (hg : ((g : ℕ) : 𝓞 F) ∈ v.asIdeal) : ((p : ℕ) : 𝓞 F) ∉ v.asIdeal := by sorry
