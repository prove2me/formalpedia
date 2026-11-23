-- Prove2me | Theorems.Thm_Formalism_UG_P_finsum_out_mul
-- name    : Formalism.UG.P.finsum_out_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:39.734308+00:00
-- url     : https://prove2.me/theorems/090439db-5614-4536-b97a-41f588b706d8
-- title:
--   P: finsum out mul
-- statement:
--   The P construction uses the finsum out mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/HeckeActMem.lean#L21-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/HeckeActMem.lean#L21-L29

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

theorem Formalism.UG.P.finsum_out_mul {M : Type} [AddCommMonoid M] (K : Subgroup G) (a : G) (F : G → M)
    (hF : ∀ (g : G) (c : K), F (g * c) = F g) :
    ∑ᶠ z : G ⧸ K, F (a * z.out) = ∑ᶠ y : G ⧸ K, F y.out := by sorry
