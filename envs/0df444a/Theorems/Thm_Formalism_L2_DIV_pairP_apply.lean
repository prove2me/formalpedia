-- Prove2me | Theorems.Thm_Formalism_L2_DIV_pairP_apply
-- name    : Formalism.L2.DIV.pairP_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:08.108319+00:00
-- url     : https://prove2.me/theorems/e4a7c34e-086e-4ae7-ab0a-11634ff20b03
-- title:
--   DIV: pair P apply
-- statement:
--   The DIV construction uses the pair P apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L466-L468
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L466-L468

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

theorem Formalism.L2.DIV.pairP_apply {K : Type} [Field K] [StarRing K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (G : ι → Matrix (Fin n) (Fin n) K) (F F' : Pol K ι n) :
    pairP lam G F F' = gramTw lam G / extNorm K lam * fockL F (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (G τ)ᵀ) F') := by sorry
