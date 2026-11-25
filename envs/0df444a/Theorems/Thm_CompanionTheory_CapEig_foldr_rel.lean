-- Prove2me | Theorems.Thm_CompanionTheory_CapEig_foldr_rel
-- name    : CompanionTheory.CapEig.foldr_rel
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:44:55.180321+00:00
-- url     : https://prove2.me/theorems/a667ec43-8c59-483c-b454-9cb1a2252722
-- title:
--   Cap Eig: foldr rel
-- statement:
--   The Cap Eig construction uses the foldr rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/Transport.lean#L14-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/Transport.lean#L14-L26

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

theorem CompanionTheory.CapEig.foldr_rel
    {Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)}
    {Eop' : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E') → (Matrix (Fin n) (Fin n) ℂ → E')}
    (Rel : (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E') → Prop)
    (hT : ∀ u a b f f', Rel f f' → Rel (Top Eop u a b f) (Top Eop' u a b f'))
    {f : Matrix (Fin n) (Fin n) ℂ → E} {f' : Matrix (Fin n) (Fin n) ℂ → E'} (h : Rel f f') :
    ∀ (t : ℕ) (u : Fin t → ℂ) (a b : Fin t → Fin n),
      Rel ((List.ofFn fun k => Top Eop (u k) (a k) (b k)).foldr (fun T h => T h) f)
        ((List.ofFn fun k => Top Eop' (u k) (a k) (b k)).foldr (fun T h => T h) f')
  := by sorry
