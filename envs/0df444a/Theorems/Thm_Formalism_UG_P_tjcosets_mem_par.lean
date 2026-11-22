-- Prove2me | Theorems.Thm_Formalism_UG_P_tjcosets_mem_par
-- name    : Formalism.UG.P.tjcosets_mem_par
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:28:26.604417+00:00
-- url     : https://prove2.me/theorems/d50d5358-71ce-425c-a5d4-90c0f763842d
-- title:
--   P: tjcosets mem par
-- statement:
--   The P construction uses the tjcosets mem par property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsFF.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsFF.lean#L73-L75

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

theorem Formalism.UG.P.tjcosets_mem_par [Finite 𝔽] (n j : ℕ) (g : GL (Fin n) 𝔽) :
    g ∈ tjcosets_par n j ↔
      ∀ a b : Fin n, (a : ℕ) < j → j ≤ (b : ℕ) → (g : Matrix (Fin n) (Fin n) 𝔽) a b = 0 := by sorry
