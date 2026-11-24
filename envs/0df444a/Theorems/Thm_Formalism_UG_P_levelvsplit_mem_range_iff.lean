-- Prove2me | Theorems.Thm_Formalism_UG_P_levelvsplit_mem_range_iff
-- name    : Formalism.UG.P.levelvsplit_mem_range_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:33:44.485954+00:00
-- url     : https://prove2.me/theorems/ac7db82b-ad66-45f4-b46a-c1055a388074
-- title:
--   P: levelvsplit mem range iff
-- statement:
--   The P construction uses the levelvsplit mem range iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelvsplit.lean#L18-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelvsplit.lean#L18-L44

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelvsplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
variable {A R : Type} [CommRing A] [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.levelvsplit_mem_range_iff (f : R →+* A) (hf : Function.Injective f) (g : GL n A) :
    g ∈ (bc (n := n) f).range ↔
      (∀ i j, (g : Matrix n n A) i j ∈ Set.range f) ∧
        ∀ i j, ((g⁻¹ : GL n A) : Matrix n n A) i j ∈ Set.range f := by sorry
