-- Prove2me | Theorems.Thm_EdgeClearGlue_hins_of_slabClear
-- name    : EdgeClearGlue.hins_of_slabClear
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:02:17.233335+00:00
-- url     : https://prove2.me/theorems/61f555a0-33ef-4c42-baf5-60b1f31ed2e9
-- title:
--   Zero-free slabs confine ball zeros to the band interior
-- statement:
--   Let $1\notin B(c,R)$ and let $c_i=\operatorname{Im}c$. Suppose
--   $0\le c_i-R$, $T_0-\delta_0\le c_i-R$, and $c_i+R\le T_1+\delta_1$.
--   If the slabs $[T_0-\delta_0,T_0]$ and $[T_1,T_1+\delta_1]$ are zero-free in
--   the critical strip, then every zeta zero $\rho$ in the ball's finite zero support satisfies
--   $$-1<\operatorname{Re}\rho<2,\qquad T_0<\operatorname{Im}\rho<T_1.$$
--   The conclusion places the support strictly inside the counting rectangle.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/EdgeClearGlue.lean#L143-L164

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
import Theorems.Thm_EdgeClearGlue_mem_ball_and_zero_of_mem_zeroFinset
import Theorems.Thm_ZetaZeroConfinement_zeta_zero_iff_completed_zero_of_im_ne
/-  EdgeClearGlue.lean -- brick K1 of the ANDURIL Arb discharge
    (telperion/docs/ANDURIL_ARB_DISCHARGE_2026-09-23.md, section 1.3: `hArbT_nonvanishing_of_edge_clear`).

    Every emitted Turing band `RHInBoxT_*.rh_in_box_*` states the canonical
    `TuringBand.BandStatement` and takes an Arb binder `hArbT` with nine conjuncts.  The first four
    are non-vanishing and confinement facts about the RvM rectangle `[-1, 2] x [T0, T1]` and the
    Blaschke ball `ball c R` that covers it:

      hnzb : ∀ x ∈ [-1, 2], ζ(x + T0 i) ≠ 0                      (H2a, bottom edge)
      hnzt : ∀ x ∈ [-1, 2], ζ(x + T1 i) ≠ 0                      (H2a, top edge)
      hnzl : ∀ y ∈ [T0, T1], ζ(-1 + y i) ≠ 0                     (H2b, left edge)
      hins : every zero of ζ in `ball c R` lies in (-1, 2) x (T0, T1)   (H2c, confinement)

    This file derives all four from
      * `ZetaZeroConfinement.zeta_zero_re_mem_strip`: an off-real zero of ζ has 0 < Re < 1;
      * the ball geometry: three rational/sqrt inequalities about c, R, T0, T1 (decidable per band);
      * two EDGE-CLEARANCE facts, the memo's E(T0, δ0) and E(T1, δ1), as zero-free SLABS on the
        OUTER side of each edge: `SlabClear (T0 - δ0) T0` and `SlabClear T1 (T1 + δ1)`, where
        `SlabClear a b` says ζ has no zero with 0 < Re < 1 and a ≤ Im ≤ b.

    H2b needs no input at all: `hnzl_discharged` proves the conjunct for EVERY `T0`, `T1`, with no
    hypotheses (off the real axis by the strip theorem; at y = 0 by ζ(-1) = -1/12).  That removes
    one binder from each of the 10,379 bands of the h280000 ladder.

    What remains numerical after this file: two one-sided slab facts per band, about the open strip
    0 < Re < 1 only.  WHY ONE-SIDED, AND HOW TALL (measured on the h280000 ladder with the float
    zero list at grid 0.01, the tight cases refined with mpmath; untrusted numerics, design only):
      * ONE-SIDED: at about 2,831 band edges a zero lies on the INNER side of the edge closer than
        the ball cap (as close as the grid resolves), so even a two-sided window of half-height
        equal to the cap would be false there.  Inner-side zeros are counted by the band; only
        the outer side must be clear, and that is all `hins` needs.
      * TALL ENOUGH, NOT TOO TALL: the slab must reach past the ball cap (δ ≥ cap; caps are 0.0574
        to 0.0922) and must stop before the nearest zero beyond the edge.  The margin between the
        two is as small as 4.3e-5 (top edge 154974: cap 0.092160, zero at 154974.092203).  So δ
        must be the band's own cap rounded up finely (emit_band_glue.py uses 1e-6); a round
        δ = 1/10 would make the slab hypothesis false at about 385 of the 10,379 bands.

    Trust: no hypotheses beyond those named in each statement; axioms
    [propext, Classical.choice, Quot.sound] (see AxiomGuardBandGlue.lean).  No `sorry`.

    conjecture1_proved = False.  This is glue for a finite verification up to a fixed height; it
    says nothing about the Riemann Hypothesis. -/




open Complex

section
namespace EdgeClearGlue
end EdgeClearGlue
open EdgeClearGlue

/-! ## Zeta off the critical strip -/











/-! ## Edge clearance: zero-free slabs -/







/-! ## Confinement of the Blaschke-ball zeros -/

theorem EdgeClearGlue.hins_of_slabClear {T0 T1 δ0 δ1 : ℝ} {c : ℂ} {R : ℝ} (hs1 : (1 : ℂ) ∉ Metric.ball c R)
    (hpos : 0 ≤ c.im - R) (hlo : T0 - δ0 ≤ c.im - R) (hhi : c.im + R ≤ T1 + δ1)
    (hE0 : SlabClear (T0 - δ0) T0) (hE1 : SlabClear T1 (T1 + δ1)) :
    ∀ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      (-1 : ℝ) < ρ.re ∧ ρ.re < 2 ∧ T0 < ρ.im ∧ ρ.im < T1 := by sorry
