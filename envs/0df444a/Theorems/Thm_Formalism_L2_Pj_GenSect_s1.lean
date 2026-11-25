-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenSect_s1
-- name    : Formalism.L2.Pj.GenSect.s1
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:47:01.939803+00:00
-- url     : https://prove2.me/theorems/b4e35948-015d-4601-b889-001da6387abd
-- title:
--   Gen Sect: s1
-- statement:
--   The Gen Sect construction uses the s1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSect.lean#L12-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSect.lean#L12-L37

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectC
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSect
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
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}

theorem Formalism.L2.Pj.GenSect.s1 [CharZero K] (hfg : (⊤ : IntermediateField K Ω).FG) (htr : Algebra.trdeg K Ω = D)
    (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0)
    (hbig : Algebra.trdeg K (IntermediateField.adjoin K (Set.range fun j => x j / x j₀)) = D) :
    (IsField (RS K Ω D m ⧸ Is K x) ∧ FiniteDimensional (KTf K D m) (RS K Ω D m ⧸ Is K x)) ∧
      ∀ (K' : Type) [Field K'] [Algebra (KTf K D m) K'],
        FiniteDimensional K' (K' ⊗[KTf K D m] (RS K Ω D m ⧸ Is K x)) ∧
          IsReduced (K' ⊗[KTf K D m] (RS K Ω D m ⧸ Is K x)) := by sorry
