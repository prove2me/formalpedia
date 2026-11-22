-- Prove2me | Theorems.Thm_Formalism_UG_P_finite_supp
-- name    : Formalism.UG.P.finite_supp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:28:09.426664+00:00
-- url     : https://prove2.me/theorems/f73b8dea-935e-4f59-bd9d-939d33499cb9
-- title:
--   P: finite supp
-- statement:
--   The P construction uses the finite supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/HeckeActMem.lean#L31-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/HeckeActMem.lean#L31-L68

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {G : Type} [Group G]

theorem Formalism.UG.P.finite_supp {k : Type} [CommRing k] (K : Subgroup G) (hK : IsCommensurated K)
    (f : G → k) (hf : f ∈ Hecke k K) : {x : G ⧸ K | f x.out ≠ 0}.Finite := by sorry
