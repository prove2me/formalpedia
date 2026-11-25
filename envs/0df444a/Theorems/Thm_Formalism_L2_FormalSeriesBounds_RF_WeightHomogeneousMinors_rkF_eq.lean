-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousMinors_rkF_eq
-- name    : Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.rkF_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:51:32.344956+00:00
-- url     : https://prove2.me/theorems/09586050-555e-48cd-bc97-2bddedd1ba44
-- title:
--   Weight Homogeneous Minors: rk F eq
-- statement:
--   The Weight Homogeneous Minors construction uses the rk F eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneRowDegrees.lean#L149-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneRowDegrees.lean#L149-L160

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowDegrees
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
open Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {T : Type} {r : T → ℕ}
  {Orb : Type} {tau : Orb → Fin 2 → ZMod d → T} {o0 : Orb} {J0 : Fin 2 → Type} [∀ g, Fintype (J0 g)]
variable (X : RowData C V d (IIof r tau o0) J0) (F : Flag X)
  (hty : ∀ g (x : IIof r tau o0 g), (X.G g).ty (Sum.inl x) = x.1)
  (std : ∀ g t (c : Fin (X.rkF g t)), ((F.en g t c).2 : ℕ) = c.val)
include hty

theorem Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.rkF_eq (g : Fin 2) (t : ZMod d) : X.rkF g t = r (tau o0 g t) := by sorry
