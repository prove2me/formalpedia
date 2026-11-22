-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_frmS_apply
-- name    : Formalism.FourierDecayAlt.P.GramProductIdentities.frmS_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:56:55.895913+00:00
-- url     : https://prove2.me/theorems/38ba75e0-17f0-41b1-a6ce-960ab8d7ad6d
-- title:
--   Gram Product Identities: frm S apply
-- statement:
--   The Gram Product Identities construction uses the frm S apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramProductIdentities.lean#L49-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramProductIdentities.lean#L49-L49

import Definitions.Def_Formalism_HermitianCurvature_PositionExpansionTopCoefficients
import Definitions.Def_Lemmata_HermitianSesquilinear_ConjEqOfNonnegReal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GramProductIdentities
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
  [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]

theorem Formalism.FourierDecayAlt.P.GramProductIdentities.frmS_apply (ρ : Rep A V) (M : SlopeTestRemainingChoices S A) (X X' : Ix S → V) : frmS ρ M X X' = frm ρ M X X' := by sorry
