-- Prove2me | Theorems.Thm_BandGlue_BandData_CapGeom_of_sqrt
-- name    : BandGlue.BandData.CapGeom.of_sqrt
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:31:42.923998+00:00
-- url     : https://prove2.me/theorems/969b2ef9-c3ba-4f17-bed5-1d108cf09549
-- title:
--   Ball-cap geometry from squared bounds
-- statement:
--   Let band data $d$ have nonzero endpoint heights $t_0,t_1$, center imaginary part
--   $c\ge0$, and radius $\sqrt q$. Let $\delta_0,\delta_1\ge0$. If
--   $$q\le c^2,\qquad 0\le c-t_0+\delta_0,\quad q\le(c-t_0+\delta_0)^2,
--   \qquad0\le t_1+\delta_1-c,\quad q\le(t_1+\delta_1-c)^2,$$
--   then the lower cap is nonnegative and the ball lies between the enlarged band heights:
--   $$0\le c-\sqrt q,\qquad t_0-\delta_0\le c-\sqrt q,\qquad
--   c+\sqrt q\le t_1+\delta_1.$$
--   These inequalities and the stated nonzero endpoints are the certificate's cap geometry.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/BandGlue.lean#L197-L211

import Definitions.Def_ArdaRH65K_Turing121_BandGlue
import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_EdgeClearGlue
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Definitions.Def_ArdaRH65K_Turing121_TuringBand
import Definitions.Def_ArdaRH65K_XiLineZeros
import Mathlib
/-  BandGlue.lean -- brick K0 of the ANDURIL Arb discharge
    (telperion/docs/ANDURIL_ARB_DISCHARGE_2026-09-23.md, section 1.3: `segBandHyp_of_bands`).

    THE GAP IT CLOSES.  The h280000 capstone
    `AllZeros_h280000_Indexed.all_nontrivial_zeros_up_to_height_280000` takes
    `hbands : ∀ k, k < 280 → SegBandHyp k`, and each `SegBandHyp k` is a list of BOX CLAIMS
    ("every zero of ζ in `[1/4000000, 3999999/4000000] x [segLo k i, segHi k i]` is on the line").
    Every box claim is the conclusion of one emitted band theorem `RHInBoxT_*.rh_in_box_*`, but the
    capstone ASSUMES the claims: nothing composes them.  This file makes the composition a theorem,
    parametric in the per-band Arb inputs, so a future evaluator only has to supply those inputs.

    CONTENTS.
      * `BandData`: the parameters of one Turing band, i.e. the arguments of the canonical
        `TuringBand.BandStatement` other than the strip.  `Stmt`, `LineHyp`, `ArbHyp`, `EnclHyp`,
        `Box`, `Inputs`.  `stmt_iff` checks, by `Iff.rfl`, that `LineHyp`/`ArbHyp` are EXACTLY the
        two binders of `BandStatement` (so `Inputs` is what `hLine`/`hArbT` ask for, verbatim).
      * `stmt_of_valid`: the band statement from its decidable side conditions (pins, ball
        geometry), via `TuringBand.turing_band_on_line`; the generic proof of every `rh_in_box_*`.
      * K0 generic: `segBandHyp_of_bands` (indexed band table: the `SegBandHyp` shape),
        `segBandHyp_of_bandList` (a `List` of bands), `ladder_of_bands` (a ladder of segments: the
        `∀ k, k < K → SegBandHyp k` shape the capstone consumes).  Bands may COVER their boxes
        (`T0 ≤ lo`, `hi ≤ T1`); the emitted ladder has equality.
      * K0 + K1: `ReducedInputs` (on-line zeros, two one-sided edge-clearance slabs, five
        enclosures) and `CapGeom` (decidable ball-cap geometry); `inputs_of_reduced`,
        `segBandHyp_of_reduced`, `ladder_of_reduced` (per-band slab heights).  With K1 the `hnzl`
        binder disappears and `hnzb`/`hnzt`/`hins` reduce to two zero-free slabs per band.
      * Certificate form: `BoxCert σ0 σ1 lo hi` (some band covering the box, with its statement
        and its inputs), constructors `of_stmt` / `of_valid` / `of_reduced`, and
        `segBandHyp_of_certs`, `ladder_of_certs`.  A future evaluator may pick its own band
        parameters here (for instance enclosures much wider than the 1e-12 Arb ones, as long as
        the pins hold), which the fixed-table form does not allow.

    The real-segment instantiation (segment 0 of the ladder, 25 bands, the real `rh_in_box_*`
    theorems) is `BandGlue_h1000.lean`.

    Trust: every theorem here is proved outright from its stated hypotheses; axioms
    [propext, Classical.choice, Quot.sound] (see AxiomGuardBandGlue.lean).  No `sorry`.

    conjecture1_proved = False.  Glue for a finite verification up to a fixed height; nothing
    here says anything about the Riemann Hypothesis. -/





open Complex

section
namespace BandGlue
end BandGlue
open BandGlue





section
namespace BandGlue.BandData
end BandGlue.BandData
open BandGlue.BandData

variable (σ0 σ1 : ℝ) (d : BandData)















variable {σ0 σ1 d}







/-! ## K1 inside the band: the reduced per-band input -/

theorem BandGlue.BandData.CapGeom.of_sqrt {δ0 δ1 : ℝ} {d : BandData} (t0 t1 cim q : ℝ)
    (hT0v : d.T0 = t0) (hT1v : d.T1 = t1) (hcv : d.c.im = cim) (hRv : d.R = Real.sqrt q)
    (ht0 : t0 ≠ 0) (ht1 : t1 ≠ 0) (hδ0 : 0 ≤ δ0) (hδ1 : 0 ≤ δ1)
    (hc0 : 0 ≤ cim) (hq0 : q ≤ cim ^ 2)
    (hlo0 : 0 ≤ cim - t0 + δ0) (hlo : q ≤ (cim - t0 + δ0) ^ 2)
    (hhi0 : 0 ≤ t1 + δ1 - cim) (hhi : q ≤ (t1 + δ1 - cim) ^ 2) :
    d.CapGeom δ0 δ1 := by sorry
