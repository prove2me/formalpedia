-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormResidues_vecEquiv_fst
-- name    : Formalism.HermitianLattices.Ext.L3.NormResidues.vecEquiv_fst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:42.754528+00:00
-- url     : https://prove2.me/theorems/eec192a7-dcd8-414f-b543-e285290975e9
-- title:
--   Norm Residues: vec Equiv fst
-- statement:
--   The Norm Residues construction uses the vec Equiv fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountSplitOne.lean#L180-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountSplitOne.lean#L180-L182

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountSplitOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open NormResidues
open Formalism.HermitianLattices.Ext.L3.NormResidues

theorem Formalism.HermitianLattices.Ext.L3.NormResidues.vecEquiv_fst {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P)
    (M : ℕ) (x : Fin M → 𝓞 K ⧸ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) (i : Fin M) :
    (vecEquiv hP hc M x).1 i = (pairLift hP hc (x i)).1 := by sorry
