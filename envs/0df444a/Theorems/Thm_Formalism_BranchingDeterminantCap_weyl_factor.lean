-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_weyl_factor
-- name    : Formalism.BranchingDeterminantCap.weyl_factor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:30.598936+00:00
-- url     : https://prove2.me/theorems/6d8fd3c7-8aac-4c68-a3ce-7365daedb60c
-- title:
--   Branching Determinant Cap: weyl factor
-- statement:
--   The Branching Determinant Cap construction uses the weyl factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Numeric.lean#L329-L354
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Numeric.lean#L329-L354

import Definitions.Def_Formalism_BranchSandwichDivisors_NormLog
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Interlace
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Numeric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.BranchingDeterminantCap

theorem Formalism.BranchingDeterminantCap.weyl_factor {n : ℕ} {nu : Fin (n + 1) → ℤ} (h : Antitone nu) (p : Fin (n + 1) × Fin (n + 1))
    (hp : p.1 < p.2) :
    1 ≤ (((nu p.1 - nu p.2 : ℤ) : ℝ) + ((p.2 : ℕ) : ℝ) - ((p.1 : ℕ) : ℝ)) /
          (((p.2 : ℕ) : ℝ) - ((p.1 : ℕ) : ℝ)) ∧
    (((nu p.1 - nu p.2 : ℤ) : ℝ) + ((p.2 : ℕ) : ℝ) - ((p.1 : ℕ) : ℝ)) /
          (((p.2 : ℕ) : ℝ) - ((p.1 : ℕ) : ℝ)) ≤ ((nu 0 - nu (Fin.last n) : ℤ) : ℝ) + (n : ℝ) := by sorry
