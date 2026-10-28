-- Prove2me | Theorems.Thm_ArctanTaylor_arctan_eq_ps_add_rem
-- name    : ArctanTaylor.arctan_eq_ps_add_rem
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:46:23.710976+00:00
-- url     : https://prove2.me/theorems/50cc6543-be6d-484a-aa3d-5431d6938b77
-- title:
--   Arctangent series with an integral remainder
-- statement:
--   For real $u$ and $N\in\mathbb N$, let $A_N(u)$ be the defined truncated
--   arctangent power sum. Then
--   $$\arctan u=A_N(u)+\int_0^u\frac{(-t^2)^N}{1+t^2}\,dt.$$
--   The formula retains the oriented integral for either sign of $u$.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/ArctanTaylor.lean#L61-L79

import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Theorems.Thm_ArctanTaylor_integral_polysum_eq_atanPS
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

theorem ArctanTaylor.arctan_eq_ps_add_rem (u : ℝ) (N : ℕ) :
    arctan u = atanPS u N + ∫ t in (0:ℝ)..u, (-(t^2))^N / (1+t^2) := by sorry
