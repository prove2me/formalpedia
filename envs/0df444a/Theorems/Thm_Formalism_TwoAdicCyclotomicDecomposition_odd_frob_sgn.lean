-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_frob_sgn
-- name    : Formalism.TwoAdicCyclotomicDecomposition.odd_frob_sgn
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T17:06:50.729353+00:00
-- url     : https://prove2.me/theorems/884ca8cc-0e8e-4e7c-9a7c-75251753137c
-- title:
--   Two Adic Cyclotomic Decomposition: odd frob sgn
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the odd frob sgn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OddEqOneOfSubOneMem.lean#L83-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OddEqOneOfSubOneMem.lean#L83-L139

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_InvLength
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition

theorem Formalism.TwoAdicCyclotomicDecomposition.odd_frob_sgn {L : Type} [Field L] [NumberField L] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : Gal(L/ℚ))
    (H : IsArithFrobAt ℤ σ P) (x : L) (c : ℤ) (hx : x ^ 2 = (c : L)) (hpc : ¬ (p : ℤ) ∣ c) :
    ((sgn σ x : ℤˣ) : ℤ) = jacobiSym c p := by sorry
