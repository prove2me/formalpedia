-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_GA_gauss_rtt
-- name    : Formalism.FourierDecayAlt.P.Mx6.GA.gauss_rtt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:29:35.470018+00:00
-- url     : https://prove2.me/theorems/53eed46f-e288-47f0-a476-6a2641e69c6d
-- title:
--   GA: gauss rtt
-- statement:
--   The GA construction uses the gauss rtt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L268-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferRtt.lean#L268-L330

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.GA
variable {B : Type*} [Ring B] [Algebra ℂ B]

theorem Formalism.FourierDecayAlt.P.Mx6.GA.gauss_rtt (D : ℂ) (hD0 : D ≠ 0) (hD1 : D ≠ 1) (hD2 : D ≠ -1) (τ τ' d d' l l' m m' : B)
    (c1 : τ' * τ = τ * τ') (c2 : d' * d = d * d') (c3 : d' * τ = τ * d') (c4 : d * τ' = τ' * d)
    (D1 : D • (τ * l' - l' * τ) = -(τ * (l - l'))) (D1s : D • (τ' * l - l * τ') = -(τ' * (l - l')))
    (D2 : D • (d * l' - l' * d) = d * (l - l')) (D2s : D • (d' * l - l * d') = d' * (l - l'))
    (E1 : D • (τ * m' - m' * τ) = (m - m') * τ) (TwistedContraction : D • (τ' * m - m * τ') = (m - m') * τ')
    (E2 : D • (d * m' - m' * d) = -((m - m') * d)) (E2VanishingOtherColumns : D • (d' * m - m * d') = -((m - m') * d'))
    (D3 : D • (l * l' - l' * l) = (l - l') * (l - l')) (E3 : D • (m * m' - m' * m) = -((m - m') * (m - m')))
    (D4 : D • (τ' * m * l' * τ - τ' * l' * m * τ) = d' * τ - τ' * d)
    (D4s : D • (τ * m' * l * τ' - τ * l * m' * τ') = τ * d' - d * τ') :
    ∀ i j k n : Fin 2,
      D • ((!![d + m * τ * l, m * τ; τ * l, τ] : Matrix (Fin 2) (Fin 2) B) i j *
            (!![d' + m' * τ' * l', m' * τ'; τ' * l', τ'] : Matrix (Fin 2) (Fin 2) B) k n -
          (!![d' + m' * τ' * l', m' * τ'; τ' * l', τ'] : Matrix (Fin 2) (Fin 2) B) k n *
            (!![d + m * τ * l, m * τ; τ * l, τ] : Matrix (Fin 2) (Fin 2) B) i j) =
        (!![d + m * τ * l, m * τ; τ * l, τ] : Matrix (Fin 2) (Fin 2) B) k j *
            (!![d' + m' * τ' * l', m' * τ'; τ' * l', τ'] : Matrix (Fin 2) (Fin 2) B) i n -
          (!![d' + m' * τ' * l', m' * τ'; τ' * l', τ'] : Matrix (Fin 2) (Fin 2) B) k j *
            (!![d + m * τ * l, m * τ; τ * l, τ] : Matrix (Fin 2) (Fin 2) B) i n := by sorry
