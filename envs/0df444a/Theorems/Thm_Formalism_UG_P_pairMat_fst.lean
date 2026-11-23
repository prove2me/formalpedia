-- Prove2me | Theorems.Thm_Formalism_UG_P_pairMat_fst
-- name    : Formalism.UG.P.pairMat_fst
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:40.086358+00:00
-- url     : https://prove2.me/theorems/372859d0-9e5e-42ad-a87c-e1273caea71a
-- title:
--   P: pair Mat fst
-- statement:
--   The P construction uses the pair Mat fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SplitUnitaryGroupIso.lean#L74-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SplitUnitaryGroupIso.lean#L74-L76

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

theorem Formalism.UG.P.pairMat_fst (X Y : Matrix n n R) : (pairMat X Y).map Prod.fst = X := by sorry
