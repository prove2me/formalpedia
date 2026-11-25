-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_headAlg_gen
-- name    : Formalism.FourierDecayAlt.P.PBG.headAlg_gen
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:10:42.257609+00:00
-- url     : https://prove2.me/theorems/0e2b6d2d-46bf-5fca-9a22-3a055116c70d
-- title:
--   PBG: head Alg gen
-- statement:
--   The PBG construction uses the head Alg gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGHeadV.lean#L10-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGHeadV.lean#L10-L173

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHead
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHeadV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal

theorem Formalism.FourierDecayAlt.P.PBG.headAlg_gen (A : Type) [Ring A] [Algebra ℂ A] (M : Type) [AddCommGroup M] [Module ℂ M] (k r m : ℕ)
    (hm : m + 2 ≤ r) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (La : A →ₗ[ℂ] M)
    (xi : Fin r → Fin (2 * r + k + 1) → ℂ) (Z : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (c c' u : ℂ)
    (hG : Formalism.REAL.GlRel E)
    (hR : ∀ (x : A) (p q : Fin (2 * r + k + 1)), p.val < q.val → q.val < r →
      La (x * E p q) = (if q.val = p.val + 1 then (1 : ℂ) else 0) • La x)
    (hZ : Z.det ≠ 0) (hc : c ≠ 0)
    (hL : ∀ (b : Fin (m + 1)) (x : A), La (E (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨b, by omega⟩) * x) =
      (c' * Z⁻¹ b (Fin.last m)) • La x)
    (hxi : ∀ (a : Fin (m + 1)) (q : Fin (2 * r + k + 1)), xi ⟨a, by omega⟩ q = if h : q.val < m + 1 then Z a ⟨q, h⟩ else 0)
    (hxl : ∀ q : Fin (2 * r + k + 1), xi ⟨m + 1, by omega⟩ q = if q.val = m + 1 then c else 0) :
    (Z.det * c)⁻¹ • La (C3.AAx k r E xi (m + 2) hm u) =
      Z.det⁻¹ • La (C3.AAx k r E xi (m + 1) (by omega) u *
          (algebraMap ℂ A (u - ((m + 1 : ℕ) : ℂ)) + E (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩))) -
        (c' * Z.det⁻¹) • La (C3.AAx k r E xi m (by omega) u) := by sorry
