-- Prove2me | Theorems.Thm_Formalism_FG_CongrVAux_coeff_subst_perturb
-- name    : Formalism.FG.CongrVAux.coeff_subst_perturb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:58.169799+00:00
-- url     : https://prove2.me/theorems/e8d8dee9-8da0-4242-b103-4397fe6bc522
-- title:
--   Congr VAux: coeff subst perturb
-- statement:
--   The Congr VAux construction uses the coeff subst perturb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CongrV.lean#L65-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CongrV.lean#L65-L119

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CongrV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.CongrVAux
open MvPowerSeries Formalism.G Formalism.LT Formalism.FG.SolveVAux
variable {R : Type u} [CommRing R] {τ : Type w}

theorem Formalism.FG.CongrVAux.coeff_subst_perturb {ι : Type v} [Fintype ι] {d : τ →₀ ℕ} (hd : d ≠ 0)
    {k : ι → MvPowerSeries τ R} (hk : ∀ i, constantCoeff (k i) = 0) (c : ι → R)
    (g : MvPowerSeries ι R) :
    coeff d (subst (fun i => k i + monomial d (c i)) g) =
      coeff d (subst k g) + ∑ i, coeff (Finsupp.single i 1) g * c i := by sorry
