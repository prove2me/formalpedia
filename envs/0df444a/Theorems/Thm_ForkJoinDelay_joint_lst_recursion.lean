-- Prove2me | Theorems.Thm_ForkJoinDelay_joint_lst_recursion
-- name    : ForkJoinDelay.joint_lst_recursion
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:33:32.319986+00:00
-- url     : https://prove2.me/theorems/c9c34d2e-a204-4197-bb42-b37a1fdb61ff
-- title:
--   §§2–3.1 — the recursion computes the joint LST of $(S_0,S_{FJ})$ exactly
-- statement:
--   Consider the fork-join network of §2: a single-server FCFS station $Q_0$ with exponential services of rate $\mu_0$, followed by two single-server FCFS stations UFJ and LFJ with exponential services of rates $\mu_1$ and $\mu_2$, which every customer leaving $Q_0$ joins simultaneously, with independent services, and leaves when both are done. A tagged customer arrives and finds $k$ customers at $Q_0$, $h_1$ at UFJ and $h_2$ at LFJ. Let $S_0$ be its sojourn time at $Q_0$ and $S_{FJ}=\max\{S_1,S_2\}$ its sojourn time in the fork-join part.
--
--   Then for all rates $\mu_0,\mu_1,\mu_2>0$, all complex $w_0,w_{FJ}$ with $\operatorname{Re}w_0\ge0$, $\operatorname{Re}w_{FJ}\ge0$, and all $k,h_1,h_2\ge0$,
--
--   $$\Psi_{k,h_1,h_2}(w_0,w_{FJ})=\mathbb E\bigl[e^{-w_0S_0-w_{FJ}S_{FJ}}\bigr]=\Psi^{\mathrm{rec}}_{k,h_1,h_2}(w_0,w_{FJ}),$$
--
--   where $\Psi^{\mathrm{rec}}$ is computed by the boundary recursion (6) for $k=0$, from the transforms $Z_{x,y}$ of (5) (maximum of independent $\Gamma(x,\mu_1)$ and $\Gamma(y,\mu_2)$ variables), and by the recursion (3) for $k\ge1$, with the coefficient $a$ in the closed form of (4) and $b,c,d$ its tail sums.
--
--   The theorem says the paper's computational method for state-dependent delay announcements in fork-join networks is exact: the joint transform of the two sojourn times, from which their distributions are recovered by numerical inversion, is a finite recursion in closed-form coefficients and the boundary transforms.
--
--   **Formalization Note** The left side is the expectation in the explicit model; the right side is defined by recursion on $k$ without reference to the model.
--
--   Differences from the source:
--   - encoding: E_{k,h1,h2}[·]: expectation given the state (k, h1, h2) at the tagged customer's arrival → expectation in an explicit FCFS construction from i.i.d. exponential services (residual services included), no arrivals after the tagged customer (IsFJModel, sojournQ0, sojournFJ); reason: the paper's own argument: residual services are exponential by memorylessness (pp.9–10) and later arrivals do not matter (p.8)
--   - reading: FJ stations may be single-, multiple- or infinite-server; 'From here on, we shall assume both stations in the FJ part have a single server' (p.8) → single-server FCFS stations UFJ and LFJ; reason: the paper fixes single servers on p.8 and (2) is the single-server formula
--   - reading: service 'rates' µ0, µ1, µ2 → 0 < µ0, µ1, µ2; reason: a rate of an exponential law is positive
--   - generalization: transform arguments w0, wFJ (domain not stated; LST on real w ≥ 0) → complex w0, wFJ with Re w0 ≥ 0, Re wFJ ≥ 0; reason: real w ≥ 0 is the special case; the paper evaluates the transform at imaginary arguments (Fourier inversion, p.13); every formula is defined there
--   - reading: (1)–(3) derived 'for the case where k,h1,h2 > 0'; p.11: (3) 'remains valid when an empty sum is defined to be zero' for h1 = 0 or h2 = 0 → every h1, h2 ≥ 0, with empty finite sums (Finset.range) for h = 0; reason: the paper's own extension on p.11 (and p.9: 'the cases h1 = 0 and h2 = 0 follow from the same analysis')
--   - encoding: a(r1,r2) defined as an integral (p.10) → a(r1,r2) in the closed form of (4) (coefA); b, c, d the tsums of it; reason: the closed form is proved in (4); milestone eq_4_coefficients states that the two agree
--   - encoding: Z_{x,y}(wFJ) := E[e^{−wFJ SFJ} | h1 = x, h2 = y] = ∫_0^∞ e^{−wFJ t} dF_{SFJ|x,y}(t) (5) → ∫ e^{−wFJ max(s,t)} d(Gamma(x,µ1) ⊗ Gamma(y,µ2)) (boundaryLST); reason: p.12 identifies (S1|h1 = x) ∼ Gamma(x,µ1), (S2|h2 = y) ∼ Gamma(y,µ2), independent; milestone sec_3_1_fj_cdf connects the two
-- source:
--   Carmeli, Yom-Tov, Boxma, State-Dependent Estimation of Delay Distributions in Fork-Join Networks, author manuscript (sha256 c8b2002d…9d1c), §§2–3.1, Eqs. (1)–(6), pp.8–13 (recursion (3), p.11; boundary recursion (6) with (5), p.12; closed form of a, Eq. (4), p.11; b, c, d, pp.10–11)

import Mathlib
import Definitions.Def_ForkJoinDelay_IsFJModel
import Definitions.Def_ForkJoinDelay_psi
import Definitions.Def_ForkJoinDelay_psiRec

open MeasureTheory ProbabilityTheory

namespace ForkJoinDelay

/-- **The joint LST of the tagged customer's sojourn times is computed exactly by the
recursion (3)/(6).**
Carmeli, Yom-Tov, Boxma, *State-Dependent Estimation of Delay Distributions in Fork-Join
Networks*, author manuscript, §§2–3.1, Eqs. (1)–(6), pp.8–13 (the recursion (3), p.11, for
`k ≥ 1`; the boundary recursion (6) with (5), p.12, for `k = 0`; the closed form of `a` in (4),
p.11; `b, c, d` as defined on pp.10–11).

In the fork-join network of §2 (single-server FCFS station `Q₀` with exponential(`µ₀`) services,
followed by single-server FCFS stations UFJ and LFJ with exponential(`µ₁`), exponential(`µ₂`)
services; every customer joins both), started at the arrival of a tagged customer who finds
`k` customers at `Q₀`, `h₁` at UFJ and `h₂` at LFJ, the joint Laplace–Stieltjes transform
`Ψ_{k,h₁,h₂}(w₀, w_FJ) = E[e^{−w₀S₀ − w_FJ S_FJ}]` equals `Ψ^rec_{k,h₁,h₂}(w₀, w_FJ)`, for
**every** `k, h₁, h₂ ≥ 0`, every rates `µ₀, µ₁, µ₂ > 0` and every complex `w₀, w_FJ` with
nonnegative real parts.

**Formalization Note.** `psi` is the expectation in the explicit model (`IsFJModel`,
`sojournQ0`, `sojournFJ`), and `psiRec` is the recursion, defined without reference to the
model. -/
theorem joint_lst_recursion {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ₀ μ₁ μ₂ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (V U G : ℕ → Ω → ℝ) (hM : IsFJModel P μ₀ μ₁ μ₂ V U G)
    (w₀ wFJ : ℂ) (hw₀ : 0 ≤ w₀.re) (hwFJ : 0 ≤ wFJ.re) (k h₁ h₂ : ℕ) :
    psi P V U G k h₁ h₂ w₀ wFJ = psiRec μ₀ μ₁ μ₂ w₀ wFJ k h₁ h₂ := by sorry

end ForkJoinDelay
