-- Prove2me | Theorems.Thm_CompanionTheory_CapEig_capC_vec
-- name    : CompanionTheory.CapEig.capC_vec
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:43:41.918519+00:00
-- url     : https://prove2.me/theorems/297464c1-923b-4376-a228-bd5c1e60505b
-- title:
--   Cap Eig: cap C vec
-- statement:
--   The Cap Eig construction uses the cap C vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/CoefEig.lean#L11-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/CoefEig.lean#L11-L38

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_FunAct
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_CoefEig
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_lam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix PI.UpqRep Formalism.FourierDecayAlt
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.CapEig

theorem CompanionTheory.CapEig.capC_vec (hI : PI.DSInfCharCap.DSInfCharCap) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
    {lam : Fin (2 * r + k + 1) → ℝ} {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Hs →L[ℂ] Hs)}
    (hlam : IsHCParam lam) (hσ : IsDSHpk k r ε lam σ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : Hs →L[ℂ] E) {v : Hs} (hv : v ∈ smoothVecs (k := k) (r := r) σ)
    {F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → E} (hF : ∀ x ∈ UH (Hpk k r), F x = L (σ x v))
    (Y : ℂ) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    PI.CapelliEig.capC (k := k) (r := r) Y F g = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • F g := by sorry
