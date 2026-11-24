-- Prove2me | Theorems.Thm_Formalism_UG_P_tjcosets_orbit_gl
-- name    : Formalism.UG.P.tjcosets_orbit_gl
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:38:02.07927+00:00
-- url     : https://prove2.me/theorems/ec408d5e-b163-4ae9-a190-3e598d9047bb
-- title:
--   P: tjcosets orbit gl
-- statement:
--   The P construction uses the tjcosets orbit gl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsFF.lean#L130-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsFF.lean#L130-L140

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {𝔽 : Type} [Field 𝔽]

theorem Formalism.UG.P.tjcosets_orbit_gl [Finite 𝔽] (n j : ℕ) :
    MulAction.orbit (GL (Fin n) 𝔽) (standardBasisTuple n j : TjcosetsFr (n - j) n 𝔽) =
      {w : TjcosetsFr (n - j) n 𝔽 | LinearIndependent 𝔽 (w : Fin (n - j) → Fin n → 𝔽)} := by sorry
