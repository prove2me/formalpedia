-- Prove2me | Theorems.Thm_Formalism_UG_P_split_mat_ext
-- name    : Formalism.UG.P.split_mat_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:22:39.242366+00:00
-- url     : https://prove2.me/theorems/305ad910-ea38-4fe2-9b17-193c898ed28a
-- title:
--   P: split mat ext
-- statement:
--   The P construction uses the split mat ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SplitUnitaryGroupIso.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SplitUnitaryGroupIso.lean#L11-L15

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

theorem Formalism.UG.P.split_mat_ext {M N : Matrix n n (R × R)} (h1 : M.map Prod.fst = N.map Prod.fst)
    (h2 : M.map Prod.snd = N.map Prod.snd) : M = N := by sorry
