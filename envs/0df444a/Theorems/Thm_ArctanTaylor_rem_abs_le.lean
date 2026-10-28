-- Prove2me | Theorems.Thm_ArctanTaylor_rem_abs_le
-- name    : ArctanTaylor.rem_abs_le
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:38:14.757319+00:00
-- url     : https://prove2.me/theorems/a20914d0-5957-439b-992d-3ae6f7bebb44
-- title:
--   A bound for the arctangent integral remainder
-- statement:
--   For $u\ge0$ and $N\in\mathbb N$,
--   $$\left|\int_0^u\frac{(-t^2)^N}{1+t^2}\,dt\right|
--   \le\frac{u^{2N+1}}{2N+1}.$$
--   This bounds the truncation error of the arctangent series.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/ArctanTaylor.lean#L83-L111

import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
/-  ArctanTaylor.lean -- ANDÚRIL A4 θ-value instrument: the reusable arctan Taylor bracket.

    The θ-value route (`ThetaValue.lean`) needs, for the Euler/Weierstrass series
    `Im log Γ(x+iy) = y·log n − Σ_k arctan(y/(x+k))` (limit form), a KERNEL box for each
    `arctan(y/(x+k))`.  This file is the reusable arctan instrument that produces those boxes,
    with NO numeric hypotheses and NO special-function anchors (no ψ, no Γ).

    ## The instrument.

    For `u ≥ 0` and any truncation order `N`,

        |arctan u − atanPS u N| ≤ u^(2N+1)/(2N+1),        atanPS u N = Σ_{j<N} (−1)^j u^(2j+1)/(2j+1).

    This is the alternating Taylor bracket, proved RIGOROUSLY from the integral representation
    `arctan u = ∫₀ᵘ (1+t²)⁻¹` (Mathlib `integral_inv_one_add_sq`) via the finite geometric
    identity `(1+t²)⁻¹ = Σ_{j<N}(−t²)^j + (−t²)^N/(1+t²)` and the elementary remainder bound
    `|∫₀ᵘ (−t²)^N/(1+t²)| ≤ ∫₀ᵘ t^(2N) = u^(2N+1)/(2N+1)`.

    Two cheap corollaries used by the tail machinery (elementary, no integral):
      * `arctan_le_self`        : `arctan u ≤ u`               (0 ≤ u)
      * `self_sub_cube_le_arctan`: `u − u³/3 ≤ arctan u`       (0 ≤ u)

    All lemmas are GENERAL in `(u, N)` — the ThetaValue driver instantiates them per term.
    Guarded: `#print axioms arctan_bracket` = {propext, Classical.choice, Quot.sound}.

    conjecture1_proved = False.  A rigorous elementary arctan enclosure, a building block, NOT a
    proof of anything about ζ.
-/





open Real intervalIntegral MeasureTheory

section
namespace ArctanTaylor
end ArctanTaylor
open ArctanTaylor



/-! ### The integral representation split. -/





/-! ### The remainder bound. -/

theorem ArctanTaylor.rem_abs_le (u : ℝ) (hu : 0 ≤ u) (N : ℕ) :
    |(∫ t in (0:ℝ)..u, (-(t^2))^N / (1+t^2))| ≤ u^(2*N+1)/(2*N+1) := by sorry
