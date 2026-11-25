-- Prove2me | Theorems.Thm_CompanionTheory_CapEig_eab_clm
-- name    : CompanionTheory.CapEig.eab_clm
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:43:28.842462+00:00
-- url     : https://prove2.me/theorems/22928afb-c3e6-5c7e-988a-df6ce2487b76
-- title:
--   Cap Eig: eab clm
-- statement:
--   The Cap Eig construction uses the eab clm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/Transport.lean#L65-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/Transport.lean#L65-L69

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

theorem CompanionTheory.CapEig.eab_clm (φ : E →L[ℂ] E') {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f) (a b : Fin n)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : φ (EabV ε a b f g) = EabV ε a b (fun x => φ (f x)) g := by sorry
