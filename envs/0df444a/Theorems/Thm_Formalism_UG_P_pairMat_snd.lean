-- Prove2me | Theorems.Thm_Formalism_UG_P_pairMat_snd
-- name    : Formalism.UG.P.pairMat_snd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:27.578619+00:00
-- url     : https://prove2.me/theorems/c85c3a59-6929-4e10-b2a7-c4c7e67098cd
-- title:
--   P: pair Mat snd
-- statement:
--   The P construction uses the pair Mat snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SplitUnitaryGroupIso.lean#L78-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SplitUnitaryGroupIso.lean#L78-L80

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SplitUnitaryGroupIso
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
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.pairMat_snd (X Y : Matrix n n R) : (pairMat X Y).map Prod.snd = Y := by sorry
