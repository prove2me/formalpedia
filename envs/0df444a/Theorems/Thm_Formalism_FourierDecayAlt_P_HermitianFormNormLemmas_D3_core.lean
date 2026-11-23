-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_D3_core
-- name    : Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D3.core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:10:35.20078+00:00
-- url     : https://prove2.me/theorems/b0335bdf-0eb6-42bf-b4b2-b1e788112d0e
-- title:
--   D3: core
-- statement:
--   The D3 construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean#L745-L834
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean#L745-L834

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D3
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
open Classical

theorem Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D3.core (A : ℕ) (CB CSt Cg CT : ℝ) (_hCB : 0 ≤ CB) (hCSt : 0 ≤ CSt) (hCg : 0 ≤ Cg) (hCT : 0 ≤ CT)
    (r f : ℕ) (b rd g TT cSt e1 m M : ℝ) (hm : m = 2 * (r : ℝ) + 2) (hM : M = m ^ 5 * f)
    (hf : 1 ≤ f) (hb : 16 ≤ b) (hrd0 : 0 < rd) (hrd : rd ≤ b) (hg1 : 1 ≤ g) (hg : g ≤ b ^ Cg)
    (hTT0 : 0 < TT) (hTT : TT ≤ b ^ (2 * CT * m)) (hc0 : 0 ≤ cSt) (hc : cSt ≤ b ^ (CSt * m ^ 3 * f))
    (he0 : 0 ≤ e1) (he : e1 ≤ 2) :
    (64 : ℝ) ^ (f * (r + 1)) * (cSt * e1 * (rd ^ (12 * r * (r + 1) * f) * TT ^ (6 * f)) *
          (g ^ f) ^ (A * (r + 1) ^ 2) * Real.exp (CB * M * Real.log b)) *
        ((rd / 2) ^ (f * (r + 1)) * g ^ (f * (r + 1) * (2 * r + 3))) ≤
      Real.exp ((2 + CSt + 1 + 12 + 12 * CT + Cg * A + CB + 1 + Cg) * M * Real.log b) := by sorry
