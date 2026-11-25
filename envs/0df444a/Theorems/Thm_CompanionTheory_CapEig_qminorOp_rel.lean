-- Prove2me | Theorems.Thm_CompanionTheory_CapEig_qminorOp_rel
-- name    : CompanionTheory.CapEig.qminorOp_rel
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:36:35.828469+00:00
-- url     : https://prove2.me/theorems/dc06839d-3d1a-5ee3-964d-c42f7a09f315
-- title:
--   Cap Eig: qminor Op rel
-- statement:
--   The Cap Eig construction uses the qminor Op rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/Transport.lean#L28-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/Transport.lean#L28-L41

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
variable {n : ℕ} {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem CompanionTheory.CapEig.qminorOp_rel
    {Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)}
    {Eop' : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E') → (Matrix (Fin n) (Fin n) ℂ → E')}
    (Rel : (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E') → Prop)
    (hT : ∀ u a b f f', Rel f f' → Rel (Top Eop u a b f) (Top Eop' u a b f'))
    (φ : E →L[ℂ] E') (g : Matrix (Fin n) (Fin n) ℂ) (hg : ∀ f f', Rel f f' → φ (f g) = f' g)
    {f : Matrix (Fin n) (Fin n) ℂ → E} {f' : Matrix (Fin n) (Fin n) ℂ → E'} (h : Rel f f')
    {t : ℕ} (a b : Fin t → Fin n) (u : ℂ) :
    φ (qminorOp Eop a b u f g) = qminorOp Eop' a b u f' g := by sorry
