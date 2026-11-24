-- Prove2me | Theorems.Thm_Formalism_UG_P_split_surjective
-- name    : Formalism.UG.P.split_surjective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:28:47.949837+00:00
-- url     : https://prove2.me/theorems/0c96a93b-7e88-4e7e-85b9-540e22f2395a
-- title:
--   P: split surjective
-- statement:
--   The P construction uses the split surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SplitUnitaryGroupIso.lean#L119-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SplitUnitaryGroupIso.lean#L119-L137

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

theorem Formalism.UG.P.split_surjective (J₁ : Matrix n n R) (hJ : IsUnit J₁.det) (h : GL n R) :
    ∃ g : GL n (R × R), g ∈ UJ (swapR R) (splitJ J₁) ∧ bc (RingHom.fst R R) g = h := by sorry
