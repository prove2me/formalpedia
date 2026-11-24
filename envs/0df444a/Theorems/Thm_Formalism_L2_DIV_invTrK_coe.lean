-- Prove2me | Theorems.Thm_Formalism_L2_DIV_invTrK_coe
-- name    : Formalism.L2.DIV.invTrK_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:20.205312+00:00
-- url     : https://prove2.me/theorems/1d1637d0-4952-48b3-9ee9-37679f8d4da5
-- title:
--   DIV: inv Tr K coe
-- statement:
--   The DIV construction uses the inv Tr K coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L280-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L280-L282

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

theorem Formalism.L2.DIV.invTrK_coe {K : Type} [Field K] {ι : Type} {n : ℕ} (g : ι → GL (Fin n) K) (τ : ι) :
    ((invTrK g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (((g τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ := by sorry
