-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_volumeFactor_mul_sq_div_le
-- name    : Formalism.HermitianLatticeCounting.P.volumeFactor_mul_sq_div_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:11:22.481611+00:00
-- url     : https://prove2.me/theorems/b9ae4340-81ca-4d0d-ad0a-a370f520dc48
-- title:
--   P: volume Factor mul sq div le
-- statement:
--   The P construction uses the volume Factor mul sq div le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LatticeSumBounds.lean#L745-L764
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LatticeSumBounds.lean#L745-L764

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P

theorem Formalism.HermitianLatticeCounting.P.volumeFactor_mul_sq_div_le (k r : ℕ) (C G T g v Dr loss' JHS Jop dim : ℝ) (hk : 1 ≤ k)
    (hC : 0 < C) (hG : 0 < G) (hT : 0 < T) (hg : 0 < g) (hv : 0 < v) (hDr : 0 < Dr)
    (hdim : 0 < dim) (hJop : 0 ≤ Jop)
    (hABS : Jop ≤ loss' * (C / (k * v)) ^ (r * (k - 2 - r)) * Dr⁻¹ ^ (k - 2 - r))
    (hrank : JHS ^ 2 ≤ dim * Jop ^ 2) :
    nv k r G T g v * JHS ^ 2 / dim ≤
      (Real.exp 1 * Real.pi / (k * v)) ^ k * (G / T) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k *
        (loss' ^ 2 * (C / (k * v)) ^ (2 * r * (k - 2 - r)) *
          Dr⁻¹ ^ (2 * (k - 2 - r))) := by sorry
