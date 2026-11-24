-- Prove2me | Theorems.Thm_Formalism_L2_DIV_fk_fock_mem
-- name    : Formalism.L2.DIV.fk_fock_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:36.765596+00:00
-- url     : https://prove2.me/theorems/fe73b439-f937-41c8-a7c9-f9204a80ae64
-- title:
--   DIV: fk fock mem
-- statement:
--   The DIV construction uses the fk fock mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/FkPderivBlockEmbNe.lean#L140-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/FkPderivBlockEmbNe.lean#L140-L145

import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkPderivBlockEmbNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open scoped Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
variable {K : Type} [Field K] (K0 : Subfield K)

theorem Formalism.L2.DIV.fk_fock_mem [StarRing K] {σ : Type} (P : MvPolynomial σ ℤ) {Q : MvPolynomial σ K}
    (hQ : Q ∈ (map (σ := σ) K0.subtype).range) : fockS (map (Int.castRingHom K) P) Q ∈ K0 := by sorry
