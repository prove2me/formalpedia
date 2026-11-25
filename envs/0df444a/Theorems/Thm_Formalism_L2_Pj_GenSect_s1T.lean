-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenSect_s1T
-- name    : Formalism.L2.Pj.GenSect.s1T
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:56:04.699789+00:00
-- url     : https://prove2.me/theorems/f9cf0181-7af6-4d98-94ef-0cdaf745c31a
-- title:
--   Gen Sect: s1 T
-- statement:
--   The Gen Sect construction uses the s1 T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectT.lean#L67-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectT.lean#L67-L259

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSect
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenSect
open MvPolynomial
open scoped TensorProduct
variable (K Ω Kl K' : Type) [Field K] [Field Ω] [Algebra K Ω] [Field Kl] [Field K'] [Algebra K Kl]
  [Algebra Kl K'] [Algebra K K'] [IsScalarTower K Kl K']
variable {K Ω Kl K'} {D m : ℕ}
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

theorem Formalism.L2.Pj.GenSect.s1T [CharZero K] (hfg : (⊤ : IntermediateField K Ω).FG) (htr : Algebra.trdeg K Ω = D)
    (v : Fin m → Ω) (k₀ : Fin m) (hv₀ : v k₀ ≠ 0)
    (hbig : Algebra.trdeg K (IntermediateField.adjoin K (Set.range fun k => v k / v k₀)) = D)
    (t : Fin (D + 1) × Fin m → K') (ht : AlgebraicIndependent K t) :
    FiniteDimensional K' (Localization.Away (tsec K Kl t v 0) ⧸ tJ K Kl t v) ∧
      IsReduced (Localization.Away (tsec K Kl t v 0) ⧸ tJ K Kl t v) := by sorry
