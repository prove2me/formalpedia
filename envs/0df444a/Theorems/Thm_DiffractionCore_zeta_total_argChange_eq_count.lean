-- Prove2me | Theorems.Thm_DiffractionCore_zeta_total_argChange_eq_count
-- name    : DiffractionCore.zeta_total_argChange_eq_count
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:04:47.81283+00:00
-- url     : https://prove2.me/theorems/4d046305-fb5d-40f4-8cc7-4d40fd34faa5
-- title:
--   Zeta argument change equals the rectangle zero count
-- statement:
--   Let $R=[\sigma_0,\sigma_1]\times[T_0,T_1]$ be ordered and contained in a ball
--   excluding $1$. Suppose zeta is nonzero on the boundary and all zeta zeros in the
--   ball lie strictly inside $R$. Then its positively oriented total argument change is
--   $$\Delta_{\partial R}\arg\zeta
--   =2\pi\sum_{\rho}\operatorname{ord}_{\rho}(\zeta),$$
--   where the finite sum is over the ball's zeta-zero support. The left side is the
--   signed sum of the four defined horizontal and vertical argument changes.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_zero_localization/lean/DiffractionCore.lean#L957-L1011

import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
import Theorems.Thm_DiffractionCore_bd_weighted_logDeriv_zeta
/-  DIFFRACTION CORE (Dyson/quasicrystal axis, QC2 brick 1): the WEIGHTED rectangle pole formula.

    The T-ladder counts zeros (`rect_winding_generic`: `Bd((·-ρ)⁻¹) = 2πi`, the `g ≡ 1` case).
    The Dyson/Weil axis needs WEIGHTED sums over zeros — `Σ_ρ g(ρ)` for analytic test weights —
    because the explicit formula IS the diffraction identity: weighted zero-sums on one side,
    Bragg peaks at `k·log p` (prime sums) on the other.  This brick proves the single-pole
    mechanism over a rectangle:

      `Bd(g·(·-ρ)⁻¹) = 2πi·g(ρ)`   (g holomorphic near the closed box, ρ strictly interior).

    Proof: the removable-singularity split `g(z)·(z-ρ)⁻¹ = dslope g ρ z + g(ρ)·(z-ρ)⁻¹` (off ρ);
    `dslope g ρ` is holomorphic ACROSS ρ (Mathlib `has_fpower_series_dslope_fslope`), so its
    boundary integral vanishes by the generic rectangle Goursat (`rect_arg_principle_generic`);
    the remainder is `g(ρ)` times the counting winding (`rect_winding_generic`).

    Downstream (QC ladder): QC2 brick 2 = finite-sum version over a zero Finset (mirrors
    `box_residue_sum_generic`); QC3 = the finite-height Guinand–Weil identity, pushing the
    right edge to `Re > 1` where Mathlib's `LSeries_vonMangoldt_eq` (`L Λ = -ζ'/ζ`) turns the
    contour into PRIME SUMS — the Bragg peaks, kernel-side.  The Archimedean term is already
    built (`ZeroFreeBridge.logDeriv_gammaR`, the θ-bridge).

    conjecture1_proved = False. -/






open Complex MeasureTheory Real
open scoped Topology

section
namespace DiffractionCore
end DiffractionCore
open DiffractionCore









/-! ## Brick 4 (P1): the prime keystone — `logDeriv ζ = −L(Λ)` on `Re s > 1`.

Mathlib's `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` supplies the arithmetic side whole:
`L(Λ) s = −ζ′(s)/ζ(s)` for `Re s > 1`.  Restated in the harness's `logDeriv` vocabulary, this is
the identity that lets `bd_weighted_logDeriv_zeta`'s RIGHT EDGE (placed in `Re > 1`) speak primes:
the edge integrand `g·logDeriv ζ` becomes `−g·Σ Λ(n) n^{−s}` — the Bragg peaks at `k·log p`,
awaiting only the series–integral interchange (P2: dominated convergence along the compact edge,
`|Λ(n)n^{−s}| = Λ(n)n^{−σ₁}` summable).  conjecture1_proved = False. -/





/-! ## Brick 5 (P2): the series–integral interchange on the right edge.

With the right edge at `Re = σ₁ > 1`, the weighted edge integral of `L(Λ)` expands TERMWISE:
`∫ g·L(Λ) = Σ'_n ∫ g·term(Λ, n)` — dominated convergence with the `y`-independent majorant
`C·‖term(Λ, σ₁, n)‖` (vertical-line norm invariance is Mathlib's `norm_term_eq`: the norm
depends only on `Re s`; summability is `LSeriesSummable_vonMangoldt` + `summable_norm_iff`).
Combined with brick 4 this makes the right edge of `bd_weighted_logDeriv_zeta` a sum of
prime-power integrals `−Σ Λ(n)·∫ g·n^{−s}` — the Bragg peaks.  conjecture1_proved = False. -/



/-! ## Brick 6 (ASSEMBLY): the finite-height explicit formula — zeros = primes + boundary.

Composing bricks 3, 4, 5: place the box's right edge at `Re = σ₁ > 1`.  Brick 3 evaluates the
weighted boundary integral as the ZERO side (`2πi·Σ d(ρ)g(ρ)` over the actual divisor); brick 4
turns the right-edge integrand into `−g·L(Λ)` pointwise; brick 5 expands it termwise into
PRIME-POWER integrals.  The result — every hypothesis explicit, every step kernel-checked:

  `2πi · Σ_ρ d(ρ)·g(ρ)  =  (bottom edge) − (top edge) − i·Σ′_n Λ(n)-term integrals − i·(left edge)`

the rectangular Guinand–Weil / explicit-formula identity at finite height: **weighted sums over
zeta zeros equal von Mangoldt (prime-power) sums plus three boundary integrals.**  The right-edge
zeta non-vanishing is DERIVED (`Re > 1`, `riemannZeta_ne_zero_of_one_le_re`), and the test-weight
edge bound is DERIVED (extreme value theorem on the compact edge) — the Arb trust surface is only:
three off-prime-side edge non-vanishings + strict interiority of the ball's zero support.

Classically the three remaining edges are estimated and sent to limits (`T0 → −∞` symmetrically,
`σ₀ → −∞` via the functional equation); here they stand as honest, explicit remainder terms.
conjecture1_proved = False. -/



/-! ## Brick 7 (W1): the Bragg amplitude in closed form.

The prime-side integrals of `rect_explicit_formula` (constant weight `g ≡ 1`) evaluate in
CLOSED FORM: the `n`-th term is a pure oscillation of frequency `log n` —

  `∫_{T0}^{T1} Λ(n)·n^{−(σ+iy)} dy  =  [term at T1 − term at T0] / (−i·log n)`,

amplitude `Λ(n)·n^{−σ}/log n`, Bragg frequency `log n` (nonzero exactly at prime powers).
This is the diffraction pattern of the zeros, prime-side, as concrete arithmetic — the first
W1 (second-axis) brick: the formula meeting computable prime data.  conjecture1_proved = False. -/



/-! ## Brick 8 (EDGES-TO-LIMITS, structural half): the reflection identities — the LEFT edge
speaks primes and Archimedean, with ZERO Arb inputs.

The classical route sends the explicit formula's remaining edges to limits via the functional
equation: `Λ(1−s) = Λ(s)` reflects the left edge (`Re < 0`) into the prime region (`Re > 1`).
Here, kernel-side:

  * `logDeriv_completedZeta_reflect` — `(log Λ)′(1−s) = −(log Λ)′(s)` (the FE, differentiated);
  * `logDeriv_zeta_add_gammaR` — the split `(log Λ)′ = (log ζ)′ + (log Γℝ)′`;
  * `logDeriv_zeta_reflect` — the ζ reflection identity;
  * `left_edge_prime_reflection` — **for `Re s < 0`, `Im s ≠ 0`:**

      `(log ζ)′(s) = L(Λ)(1−s) − (log Γℝ)′(s) − (log Γℝ)′(1−s)`

    with EVERY hypothesis derived (`s ∉ {0,1}` from `Re < 0`; `ζ(s) ≠ 0` from the strip-location
    theorem; `ζ(1−s) ≠ 0` and `Γℝ(1−s) ≠ 0` from `Re(1−s) > 1`; `Γℝ(s) ≠ 0` from `Im ≠ 0`;
    the prime keystone at `1−s`).  The LEFT edge of any explicit-formula box in `Re < 0` is
    therefore prime sums (mirrored) + two Archimedean `ψ`-integrals (`logDeriv_gammaR` expands
    them into digammas — where the θ/Binet machinery lives) — **no ζ data, no Arb input**.

    Remaining for the full classical limit: the horizontal edges as `T → ∞`, which requires the
    `|ζ′/ζ| = O(log² T)` corridor lemma (zero-avoiding heights) — genuine further analysis,
    honestly out of scope here.  conjecture1_proved = False. -/









/-! ## Brick 9 (T3 ground — the ζ-side of Riemann–von Mangoldt): the box zero-count IS the
boundary winding of `ζ′/ζ`.

The `g ≡ 1` specialization of `bd_weighted_logDeriv_zeta`: the four-segment boundary integral of
`ζ′/ζ` around the box equals `2πi · (number of ζ-zeros in the box, with multiplicity)`.  This is
the argument principle for `ζ` in closed kernel form — the LEFT side of RvM
(`N(T) = θ(T)/π + 1 + S(T)`), which classically is obtained by taking this box to the half-line
`[1/2, ∞) × [0, T]` and splitting the boundary contour into the Γ-argument (→ `θ`, our
`riemannSiegelTheta` via the Archimedean bridge) and the ζ-argument remainder (→ `πS`).  The
half-line limit + the `S`-identification are the remaining research content
(see `docs/RVM_T3_T4_SCOPING`).  conjecture1_proved = False. -/



/-! ## Brick 10 (the argument-change infrastructure — closing the T3 "true gap" branch-free).

RvM's `S(T)` was flagged as needing a continuous `arg`-along-a-path, absent from Mathlib.  But
the CONTINUOUS ARGUMENT CHANGE along a zero-avoiding path IS the imaginary part of the
log-derivative line integral — `Im ∫ f′/f = Δ arg f`, `Re ∫ f′/f = Δ log‖f‖` — with NO branch
function, exactly as `riemannSiegelTheta` was defined by an integral rather than a branch of
`logΓ`.  These definitions + the box identity (from `bd_logDeriv_zeta_eq_count` by taking `.im`)
give the argument principle in ARGUMENT-CHANGE form: total argument change around the box =
`2π · (zero-count)`.  This is the scaffold `S` sits on: as the box opens to the half-plane, the
vertical-edge argument change on the near-critical side becomes `π·S(T)` and the horizontal/Γ
contributions become `θ(T)`.  conjecture1_proved = False. -/

theorem DiffractionCore.zeta_total_argChange_eq_count
    (sigma0 sigma1 T0 T1 : ℝ) (hsig : sigma0 ≤ sigma1) (hT : T0 ≤ T1)
    (c : ℂ) (R : ℝ)
    (hbox_ball : ∀ ρ : ℂ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball c R)
    (hs1 : (1 : ℂ) ∉ Metric.ball c R)
    (hnzb : ∀ x ∈ Set.uIcc sigma0 sigma1, riemannZeta (↑x + (T0 : ℂ) * I) ≠ 0)
    (hnzt : ∀ x ∈ Set.uIcc sigma0 sigma1, riemannZeta (↑x + (T1 : ℂ) * I) ≠ 0)
    (hnzr : ∀ y ∈ Set.uIcc T0 T1, riemannZeta ((sigma1 : ℂ) + ↑y * I) ≠ 0)
    (hnzl : ∀ y ∈ Set.uIcc T0 T1, riemannZeta ((sigma0 : ℂ) + ↑y * I) ≠ 0)
    (hins : ∀ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      sigma0 < ρ.re ∧ ρ.re < sigma1 ∧ T0 < ρ.im ∧ ρ.im < T1) :
    argChangeHoriz riemannZeta T0 sigma0 sigma1
        - argChangeHoriz riemannZeta T1 sigma0 sigma1
        + argChangeVert riemannZeta sigma1 T0 T1
        - argChangeVert riemannZeta sigma0 T0 T1
      = 2 * π * ∑ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
          (((MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ : ℤ) : ℝ) := by sorry
