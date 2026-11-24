-- Prove2me | Theorems.Thm_Formalism_L2_DIV_fk_fock_prod
-- name    : Formalism.L2.DIV.fk_fock_prod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:14.960978+00:00
-- url     : https://prove2.me/theorems/543aa63d-6e59-47df-9882-132c88fabfaa
-- title:
--   DIV: fk fock prod
-- statement:
--   The DIV construction uses the fk fock prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/FkPderivBlockEmbNe.lean#L67-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/FkPderivBlockEmbNe.lean#L67-L86

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
variable {K : Type} [Field K] [StarRing K] {ι : Type} {n : ℕ}

theorem Formalism.L2.DIV.fk_fock_prod (s : Finset ι) (f g : ι → MvPolynomial (Fin n × Fin n) K) :
    fockL (∏ τ ∈ s, Formalism.GradedWeylDivisibility.blockEmb K τ (f τ)) (∏ τ ∈ s, Formalism.GradedWeylDivisibility.blockEmb K τ (g τ)) =
      ∏ τ ∈ s, fockL (f τ) (g τ) := by sorry
