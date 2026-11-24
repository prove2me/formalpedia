-- Prove2me | Theorems.Thm_Formalism_L2_DIV_mem_transLat_gLat
-- name    : Formalism.L2.DIV.mem_transLat_gLat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:30.056258+00:00
-- url     : https://prove2.me/theorems/70ebf599-f559-4133-9bb0-f1c72497752f
-- title:
--   DIV: mem trans Lat g Lat
-- statement:
--   The DIV construction uses the mem trans Lat g Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L603-L616
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L603-L616

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}

theorem Formalism.L2.DIV.mem_transLat_gLat (lam : ι → DomWeight n) (T : Submodule (𝓞 K) (Pol K ι n))
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (g : ι → GL (Fin n) K) (F : Pol K ι n) :
    F ∈ transLat lam T (fun τ => gLat (g τ) (M τ)) ↔ actP lam g⁻¹ F ∈ transLat lam T M := by sorry
