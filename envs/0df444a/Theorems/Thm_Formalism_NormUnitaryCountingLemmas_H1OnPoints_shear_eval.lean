-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_H1OnPoints_shear_eval
-- name    : Formalism.NormUnitaryCountingLemmas.H1OnPoints.shear_eval
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:16:33.636277+00:00
-- url     : https://prove2.me/theorems/eab01688-5cbb-4c7a-93fb-eda47f02cd20
-- title:
--   H1 On Points: shear eval
-- statement:
--   The H1 On Points construction uses the shear eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NatDegreeAevalLe.lean#L40-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NatDegreeAevalLe.lean#L40-L52

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NatDegreeAevalLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.H1OnPoints
variable {R : Type*} [CommRing R]

theorem Formalism.NormUnitaryCountingLemmas.H1OnPoints.shear_eval {S : Type*} [CommRing S] [Algebra R S] {N n : ℕ} (i j : Fin N)
    (y : Fin N × Fin n → S) (s : S) (G : MvPolynomial (Fin N × Fin n) R) :
    Polynomial.eval₂ (aeval y).toRingHom s (shear R i j G) =
      aeval (fun p => y p + if p.1 = j then s * y (i, p.2) else 0) G := by sorry
