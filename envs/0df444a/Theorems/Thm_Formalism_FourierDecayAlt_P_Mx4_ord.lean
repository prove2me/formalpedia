-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_ord
-- name    : Formalism.FourierDecayAlt.P.Mx4.ord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:47:10.661567+00:00
-- url     : https://prove2.me/theorems/488141d8-8ea9-47b5-a848-63655ef34220
-- title:
--   Mx4: ord
-- statement:
--   The Mx4 construction uses the ord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L311-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L311-L341

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx4
variable {r : ℕ}

theorem Formalism.FourierDecayAlt.P.Mx4.ord (k : ℕ) (u u' ρ : ℕ → ℝ) (hI : I.Interlaces k u u' ρ) (l : ℕ) (hl : l ∈ Icc 1 (k - 1)) :
    (∀ i ∈ Icc 1 k, i ≤ l → u l ≤ u i ∧ u' l ≤ u' i) ∧ (∀ i ∈ Icc 1 k, l < i → u i ≤ u (l + 1) ∧ u' i ≤ u' (l + 1)) ∧
    (∀ j ∈ Icc 1 (k - 1), j < l → u l + 1 / 2 ≤ ρ j ∧ u' l + 1 / 2 ≤ ρ j) ∧
    (∀ j ∈ Icc 1 (k - 1), l < j → ρ j + 1 / 2 ≤ u (l + 1) ∧ ρ j + 1 / 2 ≤ u' (l + 1)) := by sorry
