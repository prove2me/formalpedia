-- Prove2me | Theorems.Thm_CompanionTheory_CapEig_ec_congr
-- name    : CompanionTheory.CapEig.ec_congr
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:43:06.8688+00:00
-- url     : https://prove2.me/theorems/e95e357a-d2b7-5bfb-9511-65db3157bc3a
-- title:
--   Cap Eig: ec congr
-- statement:
--   The Cap Eig construction uses the ec congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/Transport.lean#L50-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/Transport.lean#L50-L54

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_Smooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_Transport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open CompanionTheory CompanionTheory.CapEig
variable {n : ℕ} {ε : Fin n → Bool} {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem CompanionTheory.CapEig.ec_congr {f f' : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → f g = f' g)
    (Z : Matrix (Fin n) (Fin n) ℂ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : EcV ε Z f g = EcV ε Z f' g := by sorry
