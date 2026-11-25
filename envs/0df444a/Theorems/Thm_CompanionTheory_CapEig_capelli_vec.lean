-- Prove2me | Theorems.Thm_CompanionTheory_CapEig_capelli_vec
-- name    : CompanionTheory.CapEig.capelli_vec
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:49:11.086909+00:00
-- url     : https://prove2.me/theorems/6b68b3d5-f79a-579d-bd38-6a573ad6cf38
-- title:
--   Cap Eig: capelli vec
-- statement:
--   The Cap Eig construction uses the capelli vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/FunAct.lean#L77-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/FunAct.lean#L77-L87

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_Transport
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_FunAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants PI.DSInfCharCap
noncomputable section
open CompanionTheory CompanionTheory.CapEig
variable {n : ℕ} {ε : Fin n → Bool} {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  {σ : Matrix (Fin n) (Fin n) ℂ → (Hs →L[ℂ] Hs)}

theorem CompanionTheory.CapEig.capelli_vec (hm : ∀ a b, inUJ ε a → inUJ ε b → σ (a * b) = (σ a).comp (σ b)) {v : Hs}
    (hv : SmoothOnGV ε fun x => σ x v) (u : ℂ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    capelli ε u (fun x => σ x v) g = σ g (actU ε σ (qdet (Egl n) u) v) := by sorry
