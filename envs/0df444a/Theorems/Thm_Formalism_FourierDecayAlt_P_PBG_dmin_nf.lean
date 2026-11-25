-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_dmin_nf
-- name    : Formalism.FourierDecayAlt.P.PBG.dmin_nf
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:59:34.073612+00:00
-- url     : https://prove2.me/theorems/1ccca5be-8818-479a-9b81-059b6ab0fbd6
-- title:
--   PBG: dmin nf
-- statement:
--   The PBG construction uses the dmin nf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BaseIndexConstantInjective.lean#L211-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BaseIndexConstantInjective.lean#L211-L223

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BaseIndexConstantInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Q.Mx k r)}

theorem Formalism.FourierDecayAlt.P.PBG.dmin_nf (z z' : Fin (2 * r + k + 1) → ℂ) (x₁ : Q.Mx k r) (i0 s : ℕ) (hh : Matrix (Fin i0) (Fin i0) ℂ) (τ : ℂ)
    (hj : i0 + s ≤ r)
    (hnf : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < i0 + s →
      xi0 x₁ a p = if p.val < i0 + s then C3.Zb i0 s hh τ a.val p.val else 0)
    (n : ℕ) (hn : n ≤ i0 + s) :
    Dmin k r z z' x₁ ⟨n, by omega⟩ = C3.Dlead i0 s hh τ n := by sorry
