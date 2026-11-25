-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_tendsto_pairD
-- name    : Formalism.FourierDecayAlt.P.PBK.tendsto_pairD
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:01:26.749026+00:00
-- url     : https://prove2.me/theorems/01006e4e-dc6e-59cb-8b55-c4f1eb707a8a
-- title:
--   PBK: tendsto pair D
-- statement:
--   The PBK construction uses the tendsto pair D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TendstoSmulCocompact.lean#L107-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TendstoSmulCocompact.lean#L107-L147

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermRealisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastBlockDecay
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormOfMemRootSetOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoIntegralPsiMoving
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoSmulCocompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem Formalism.FourierDecayAlt.P.PBK.tendsto_pairD {s : ℕ} (hs : s ≠ 0) {β : ℂ} (hβ : β ≠ 0) {ε : ℂ} (hε : ‖ε‖ = 1) {bt bt' : ℂ → H}
    (hb : MemLp (bz s bt) 2 volume) (hb' : MemLp (bz s bt') 2 volume) {α : Type} {l : Filter α}
    (x x' ρ : α → ℂ) (σ : ℂ) (hρ0 : ∀ᶠ a in l, ρ a ≠ 0) (hρ : Tendsto ρ l (𝓝 1))
    (hsh : Tendsto (fun a => (s : ℂ) * (ρ a * x' a - x a)) l (𝓝 σ))
    (hne : ∀ ζ ∈ G.rootSet s 1, ζ ≠ 1 → Tendsto (fun a => ζ * ρ a * x' a - x a) l (cocompact ℂ)) :
    Tendsto (fun a => pairD s β ε bt bt' (x a) (x' a) (ρ a)) l
      (𝓝 (∫ z, G.psi β (σ * z) • ⟪bz s bt z, bz s bt' z⟫_ℂ)) := by sorry
