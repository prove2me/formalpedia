-- Prove2me | Theorems.Thm_Formalism_L2_SG_Sub_mem_stabT
-- name    : Formalism.L2.SG.Sub.mem_stabT
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:01:58.054438+00:00
-- url     : https://prove2.me/theorems/687598ca-68e6-4fb5-aeda-5c3e4aaa19ad
-- title:
--   Sub: mem stab T
-- statement:
--   The Sub construction uses the mem stab T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FundamentalEquivalence/LevelIntersectParabolic.lean#L47-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FundamentalEquivalence/LevelIntersectParabolic.lean#L47-L55

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_LevelIntersectParabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Sub
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem Formalism.L2.SG.Sub.mem_stabT {a : ℕ} (X : Fin a → Fin n → E) (g : HA R σ J) :
    g ∈ stabT R σ J X ↔ ∀ b, lin R σ J g (ratV (F := F) R (X b)) = ratV (F := F) R (X b) := by sorry
