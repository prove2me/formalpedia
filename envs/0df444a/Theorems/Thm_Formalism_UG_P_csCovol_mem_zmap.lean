-- Prove2me | Theorems.Thm_Formalism_UG_P_csCovol_mem_zmap
-- name    : Formalism.UG.P.csCovol_mem_zmap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:29.758203+00:00
-- url     : https://prove2.me/theorems/c726d845-d9e8-4a3d-9b6b-fce444e2eea5
-- title:
--   P: cs Covol mem zmap
-- statement:
--   The P construction uses the cs Covol mem zmap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsCovol.lean#L84-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsCovol.lean#L84-L89

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsCovol
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module NumberField Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) {N : ℕ}
  (ι : V →+ EuclideanSpace ℝ (Fin N))

theorem Formalism.UG.P.csCovol_mem_zmap (M : Submodule (𝓞 K) V) (v : EuclideanSpace ℝ (Fin N)) :
    v ∈ Formalism.HermitianLatticesTheory.zmap ι M ↔ ∃ y ∈ M, ι y = v := by sorry
