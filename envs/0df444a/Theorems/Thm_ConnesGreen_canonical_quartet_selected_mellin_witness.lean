-- Prove2me | Theorems.Thm_ConnesGreen_canonical_quartet_selected_mellin_witness
-- name    : ConnesGreen.canonical_quartet_selected_mellin_witness
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T06:30:16.770555+00:00
-- url     : https://prove2.me/theorems/bcb33458-27f3-45be-a3c7-d5e5692e2853
-- title:
--   An off-line actual-zero quartet has an original physical negative Mellin packet witness
-- statement:
--   For an original actual zeta zero $\rho$ off the critical line, we construct an ORIGINAL supported test $g$ on a positive finite window $t$, with the ORIGINAL quartet Mellin packet values, satisfying
--   $$\|P_t^*x\|^2-\|M_{t,Q}^*x\|^2<0,\quad\|B_{t,Q}^*x\|^2<\tfrac12,\quad
--   \operatorname{Re}W(g*\mathrm{starInv}(g))<-\tfrac12.$$
--   Here $Q$ is exactly the native reflection/conjugation orbit of the ACTUAL ZERO SUBTYPE and $x$ is the unchanged original source embedding of problemOneL(g). The accepted quartet coefficient-energy separator provides the same test with its prescribed Mellin values, full complementary coefficient energy below one half and Weil value below minus one half. Compact support supplies a finite positive original support window without changing the function. A closed quartet-membership equivalence explicitly identifies the native subtype orbit with the public theorem's four complex points, retaining duplicates according to Finset equality. Original reflection closure and the closed background bound then give the asserted background norm bound. Full arithmetic and exact negative-analysis partition force selected negativity. The original interpolation values remain attached to this same test; no enumeration equivalence or right-endpoint location is assumed. This is a derived Mellin-witness theorem, not a replacement of the original Dirichlet-analysis witness statement.
-- source:
--   monocap-tech/weil at 68011f0aa80779d1735ecbe344b0314d03cd3de5; WeilDefect/Connes/CoefficientPhysicalWitness.lean (new additive margin and witness declarations); original CanonicalGreenBackground, CanonicalGreenMarkerLimit and CriticalWindowBoundary declarations retained.

import Definitions.Def_ConnesGreen_original_quartet
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
import Definitions.Def_ConnesGreen_small_support_constants
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open ConnesRZQuartet

theorem ConnesGreen.canonical_quartet_selected_mellin_witness
    (ρ : CriticalZeros) (hoff : ρ.1.re ≠ 1 / 2) :
    ∃ t : ℝ, ∃ ht : 0 < t, ∃ g : ℝ → ℂ, SupportedTest t g ∧
      (∀ τ ∈ ConnesRZQuartet.quartet ρ, mellinHat g τ.1 = ConnesRZQuartet.packetValues ρ.1 τ.1) ∧
      (‖(canonicalPositiveSynthesis t ht).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 -
        ‖(canonicalSelectedSynthesis t ht (ConnesRZQuartet.quartet ρ)).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 < 0) ∧
      (‖(canonicalBackgroundSynthesis t ht (ConnesRZQuartet.quartet ρ)).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 < 1 / 2) ∧
      (weilDistribution (conv g (starInv g))).re < -(1 / 2) := by sorry
