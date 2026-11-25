-- Prove2me | Theorems.Thm_CompanionTheory_CapEig_capelli_clm
-- name    : CompanionTheory.CapEig.capelli_clm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:42:55.082371+00:00
-- url     : https://prove2.me/theorems/db67fa0d-6511-5778-af42-664cc8bafc4b
-- title:
--   Cap Eig: capelli clm
-- statement:
--   The Cap Eig construction uses the capelli clm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/Transport.lean#L71-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/Transport.lean#L71-L83

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

theorem CompanionTheory.CapEig.capelli_clm (φ : E →L[ℂ] E') {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f) (u : ℂ)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : φ (capelli ε u f g) = capelli ε u (fun x => φ (f x)) g := by sorry
