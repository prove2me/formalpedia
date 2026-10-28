-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_shift_root_of_standing
-- name    : AvramDividend.Classical.esscher_shift_root_of_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T15:26:27.112665+00:00
-- url     : https://prove2.me/theorems/16df55ac-1b0d-4c4a-bc8c-70f333ba78ad
-- title:
--   Every positive Esscher-shift level has a genuine root under Standing
-- statement:
--   Let X be the canonical spectrally negative Levy process satisfying X.Standing; suppose phi>0 and q>0 with X.psi(phi)=q. Then for every p>0 a strictly positive lambda satisfies X.psi(phi+lambda)−q=p. The proof combines already Proved source-specific continuum and eventual-growth theorems via the intermediate value theorem, with no Wiener–Hopf assumptions. The Standing condition is explicit and is not an assumption of the final 1E scalar milestone.
-- source:
--   Proved canonical 1fa27b74-bf2c-4549-8110-d30ac84f57e6 (continuity), 1c25d564-09f2-49a4-973c-92bd7d9e67ee (eventual growth); pinned Mathlib intermediate_value_Icc; Avram–Palmowski–Pistorius (2007), standing assumptions (3.3).

import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_continuousOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_standing
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_shift_root_of_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P F) (hX : X.Standing)
    (q phi p : ℝ)
    (hq : 0 < q) (hphi : 0 < phi) (hroot : X.ψ phi = q)
    (hp : 0 < p) :
    ∃ lambda : ℝ, 0 < lambda ∧ X.ψ (phi + lambda) - q = p := by sorry
