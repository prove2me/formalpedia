-- Prove2me | Theorems.Thm_Formalism_L2_DIV_fockL_monomial_left
-- name    : Formalism.L2.DIV.fockL_monomial_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:20.010822+00:00
-- url     : https://prove2.me/theorems/790eaee5-d5bb-4717-979b-351ea641ac5b
-- title:
--   DIV: fock L monomial left
-- statement:
--   The DIV construction uses the fock L monomial left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L339-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L339-L342

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
variable {K : Type} [Field K] [StarRing K]

theorem Formalism.L2.DIV.fockL_monomial_left {σ : Type} (u : σ →₀ ℕ) (c : K) (g : MvPolynomial σ K) :
    fockL (monomial u c) g = star c * g.coeff u * (mfact u : K) := by sorry
