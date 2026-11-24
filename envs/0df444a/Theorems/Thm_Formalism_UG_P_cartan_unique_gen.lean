-- Prove2me | Theorems.Thm_Formalism_UG_P_cartan_unique_gen
-- name    : Formalism.UG.P.cartan_unique_gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:08:03.405836+00:00
-- url     : https://prove2.me/theorems/7a67e680-f750-4d3b-95a0-ab2fff53644f
-- title:
--   P: cartan unique gen
-- statement:
--   The P construction uses the cartan unique gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Cartan.lean#L190-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Cartan.lean#L190-L213

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] (O : Subring L) {Γ : Type} [LinearOrderedCommGroupWithZero Γ]

theorem Formalism.UG.P.cartan_unique_gen (val : Valuation L Γ) (hO : ∀ x, x ∈ O ↔ val x ≤ 1) (ϖ : L)
    (hϖ0 : ϖ ≠ 0) (hϖ : val ϖ < 1) {m : ℕ} (a a' : Fin m → ℤ) (ha : Antitone a)
    (ha' : Antitone a') (k₁ : GL (Fin m) L) (hk₁ : k₁ ∈ GLint (Fin m) O)
    (k₂ : GL (Fin m) L) (hk₂ : k₂ ∈ GLint (Fin m) O)
    (h : (k₁ : Matrix (Fin m) (Fin m) L) * Matrix.diagonal (fun i => ϖ ^ a i) *
      (k₂ : Matrix (Fin m) (Fin m) L) = Matrix.diagonal (fun i => ϖ ^ a' i)) : a = a' := by sorry
