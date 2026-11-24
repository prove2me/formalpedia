-- Prove2me | Theorems.Thm_Formalism_UG_P_tjcosets_exists_smul
-- name    : Formalism.UG.P.tjcosets_exists_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:28:30.275284+00:00
-- url     : https://prove2.me/theorems/10d8c01b-e44b-4e48-b1a6-74a61e99a471
-- title:
--   P: tjcosets exists smul
-- statement:
--   The P construction uses the tjcosets exists smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsFF.lean#L118-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsFF.lean#L118-L128

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

theorem Formalism.UG.P.tjcosets_exists_smul [Finite 𝔽] (n j : ℕ) (w : TjcosetsFr (n - j) n 𝔽)
    (hw : LinearIndependent 𝔽 (w : Fin (n - j) → Fin n → 𝔽)) :
    ∃ g : GL (Fin n) 𝔽, g • (standardBasisTuple n j : TjcosetsFr (n - j) n 𝔽) = w := by sorry
