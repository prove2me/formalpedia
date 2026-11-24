-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_core
-- name    : Formalism.FourierDecayAlt.P.ScalarCastIdentities.core
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:09:12.566115+00:00
-- url     : https://prove2.me/theorems/ef91df5c-c861-4deb-8760-24642883ec5e
-- title:
--   Scalar Cast Identities: core
-- statement:
--   The Scalar Cast Identities construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AlgebraicQuantumDeterminant.lean#L13-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AlgebraicQuantumDeterminant.lean#L13-L67

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmMove
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AlgebraicQuantumDeterminant
import Theorems.Thm_Formalism_FourierDecayAlt_P_B1_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ScalarCastIdentities
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem Formalism.FourierDecayAlt.P.ScalarCastIdentities.core {A ι : Type*} [Ring A] [Fintype ι] (y η : ι → A) (C : A) (m1 m0 mm : ι → ι → A)
    (n0 nm : ι → ι → ι → ι → A)
    (hyη : ∀ a b, y a * η b = η b * y a)
    (J : ∀ i q l p, m1 i l * m0 q p - m1 q l * m0 i p = C * n0 i q l p)
    (DV : ∀ j, C * y j = y j * C - ∑ l, y l * m1 j l)
    (MC : ∀ q p i, m0 q p * η i - η i * m0 q p = ∑ a, n0 a q i p * η a)
    (BaseTypeSubspacesMapOntoBothSides : ∀ j, ∑ i, η i * mm i j = ∑ i, m0 i j * η i)
    (PairingFactorsThroughPeriods : ∀ j, ∑ i, η i * m0 i j = ∑ i, m1 i j * η i)
    (L3 : ∀ q c p, ∑ a, η a * nm a q c p = ∑ a, n0 a q c p * η a) (q p : ι) :
    C * (∑ a, ∑ c, η a * y c * nm a q c p) + (∑ j, y j * m1 q j) * (∑ i, η i * mm i p) =
      (∑ i, ∑ j, η i * y j * m0 i j) * m0 q p := by sorry
