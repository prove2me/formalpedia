-- Prove2me | Theorems.Thm_CurrentAFT_RationalPackedRootProgram_current_error_raw
-- name    : CurrentAFT.RationalPackedRootProgram.current_error_raw
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T19:45:52.430762+00:00
-- url     : https://prove2.me/theorems/09e1867a-1937-48cd-b5f3-a00ef781bc5d
-- title:
--   Raw coefficient error of the rational packed-root program
-- statement:
--   Fix security parameter $\lambda$, precision $B$, order $R\ge1$, queue value $a\in\mathbb Z$, and source counts $r,s\in\mathbb N$. Choose a tagged selection, a finite set of tagged block indices of cardinality $k$ at most the family body size, and a bijective layout from block indices to cycle vertices. Fix primary-source colors and safe body-source colors. Assume `PrecisionBudget` and, writing $L,d,q$ for the family base, dimension and modulus and $\varepsilon=2^{-B}$,
--   $$\varepsilon\le(4L)^{-1},\qquad64Ld\varepsilon\le(4q)^{-1}.$$
--   For every admissible truncated arity and every primary-color and safe-center tuple, the interpreted output of the rational packed-root program differs from the exact root-response coefficient evaluated on the actual weighted-point kernel by at most
--   $$E_{\mathrm{raw}}(\lambda,R,r,s,g,k)\varepsilon.$$
--   Here $g$ is `groupCount` of the chosen selection and tagged set, and $E_{\mathrm{raw}}$ is the explicit function `RationalPackedRootProgram.rawErrorConstant`. The numerical program uses `actualMetadata` of that same selection and tagged set. This is the coefficientwise approximation statement before subsequent aggregation and normalization.
-- source:
--   Local manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/CurrentAFT/RationalPackedRootApproximation.lean, lines 85-149. Exact native theorem type with the complete oracle-selected proof dependency cluster. Source SHA256 bfb6b5d7724f72d13fbfa11caeede5d925963d8c4d47d4583c61927fccddfc4c.

import Definitions.Def_InfoLossLAR_NativeBundle_12

















section



/-! # The native rational joint sum approximates the actual response data -/
namespace CurrentAFT.RationalPackedRootProgram
open AFT TaggedSelection PairedRootPlacement CycleRootExpansion ActualControls
  ControlCoordinates GradedControlAlgebra RationalActualFamilyApproximation
open ActualBlockFock (BlockIndex)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedApproxFinDecidableEq

attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedApproxSafeDecidableEq

attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedApproxSumDecidableEq

attribute [local instance] _root_.CurrentAFT.RationalPackedRootProgram.packedApproxSigmaDecidableEq

attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount rootReference









set_option maxRecDepth 8192

theorem _root_.CurrentAFT.RationalPackedRootProgram.current_error_raw {security r s : ℕ} (bits order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (layout : BlockIndex security ≃ Vertex security) (hroom : tagged.card ≤ Parameters.bodySize security)
    (sourcePrimary : Fin r → Palette security) (sourceBody : Fin s → SafePalette security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤
      1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (current security bits order queue (actualMetadata selection tagged)
        (fun index => (sourcePrimary index).val) (fun index => (sourceBody index).val.val)) arity colors centers -
      data security order (ActualRootResponse.response order horder queue selection tagged layout
        (WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody)) arity colors centers| ≤
      rawErrorConstant security order r s (groupCount selection tagged) tagged.card*(1/(2:ℝ)^bits) := by sorry
