-- Prove2me | Theorems.Thm_Formalism_UG_P_split_injective
-- name    : Formalism.UG.P.split_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:17.965408+00:00
-- url     : https://prove2.me/theorems/f115f6ca-1a0b-4e54-bbab-e8a577898ec3
-- title:
--   P: split injective
-- statement:
--   The P construction uses the split injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SplitUnitaryGroupIso.lean#L90-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SplitUnitaryGroupIso.lean#L90-L117

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

theorem Formalism.UG.P.split_injective (J₁ : Matrix n n R) (hJ : IsUnit J₁.det) (g g' : GL n (R × R))
    (hg : g ∈ UJ (swapR R) (splitJ J₁)) (hg' : g' ∈ UJ (swapR R) (splitJ J₁))
    (h : (g : Matrix n n (R × R)).map Prod.fst = (g' : Matrix n n (R × R)).map Prod.fst) :
    g = g' := by sorry
