-- Prove2me | Theorems.Thm_Formalism_UG_P_tjcosets_orbit_par
-- name    : Formalism.UG.P.tjcosets_orbit_par
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:37:59.251934+00:00
-- url     : https://prove2.me/theorems/46401ff3-10f5-422e-86d8-6b316ae144a7
-- title:
--   P: tjcosets orbit par
-- statement:
--   The P construction uses the tjcosets orbit par property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsFF.lean#L163-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsFF.lean#L163-L192

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

theorem Formalism.UG.P.tjcosets_orbit_par [Finite 𝔽] (n j : ℕ) :
    MulAction.orbit (tjcosets_par (𝔽 := 𝔽) n j) (standardBasisTuple n j : TjcosetsFr (n - j) n 𝔽) =
      {w : TjcosetsFr (n - j) n 𝔽 | LinearIndependent 𝔽 (w : Fin (n - j) → Fin n → 𝔽) ∧
        ∀ i (a : Fin n), (a : ℕ) < j → w i a = 0} := by sorry
