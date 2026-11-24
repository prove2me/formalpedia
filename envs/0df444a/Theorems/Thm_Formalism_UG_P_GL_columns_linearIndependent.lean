-- Prove2me | Theorems.Thm_Formalism_UG_P_GL_columns_linearIndependent
-- name    : Formalism.UG.P.GL_columns_linearIndependent
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:13:24.287881+00:00
-- url     : https://prove2.me/theorems/87785cd6-88dc-4dd6-9217-759baab16dc2
-- title:
--   P: GL columns linear Independent
-- statement:
--   The P construction uses the GL columns linear Independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsFF.lean#L114-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsFF.lean#L114-L116

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

theorem Formalism.UG.P.GL_columns_linearIndependent [Finite 𝔽] (n j : ℕ) (g : GL (Fin n) 𝔽) :
    LinearIndependent 𝔽 (fun i => (g : Matrix (Fin n) (Fin n) 𝔽).col (tjcosets_idx n j i)) := by sorry
