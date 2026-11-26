-- Prove2me | Theorems.Thm_EdenVerified_s01_basis_and_norm
-- name    : EdenVerified.s01_basis_and_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:20:59.48726+00:00
-- url     : https://prove2.me/theorems/470a5fe5-0fbe-5c8c-b883-dc67a245702f
-- title:
--   Eden Verified: s01 basis and norm
-- statement:
--   Growth rates of fixed initial basis wedges.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L147-L159
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L147-L159

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.s01_basis_and_norm (c : ℝ) (p : PhaseSpace) (k : ℕ) :
    (∀ s : ExteriorIndex k, ‖initialExteriorBasisVector k p s‖ = 1 ∧
      exteriorGrowthRate k c p (initialExteriorBasisVector k p s) =
        ∑ j ∈ s.val, factorExponents c p j) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ v : ExteriorSpace k,
      ‖exteriorEvolution k c t p v‖ ^ 2 = ∑ s : ExteriorIndex k,
        (exteriorFactor k (derivativeFactors c t p) s *
          exteriorInitialCoordinates k p v s) ^ 2) := by sorry
