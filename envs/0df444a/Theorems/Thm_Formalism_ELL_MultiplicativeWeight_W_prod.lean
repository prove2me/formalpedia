-- Prove2me | Theorems.Thm_Formalism_ELL_MultiplicativeWeight_W_prod
-- name    : Formalism.ELL.MultiplicativeWeight.W_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:07.146798+00:00
-- url     : https://prove2.me/theorems/3b1a0b18-7eca-4043-a7a3-28614a938a01
-- title:
--   Multiplicative Weight: W prod
-- statement:
--   The Multiplicative Weight construction uses the W prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CompExp.lean#L58-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CompExp.lean#L58-L72

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_CompExpWeight
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CompExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries IsUltrametricDist
universe u
open Formalism Formalism.ELL Formalism.ELL.MultiplicativeWeight
variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ : Type} (c : ℝ)
variable {c}

theorem Formalism.ELL.MultiplicativeWeight.W_prod (hc : 0 < c) (hc1 : c ≤ 1) (a : σ → MvPowerSeries σ K) (ha : ∀ i, W c 1 (a i))
    (d : σ →₀ ℕ) : W c (d.degree : ℤ) (d.prod fun s n => a s ^ n) := by sorry
