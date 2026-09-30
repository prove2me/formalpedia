-- Prove2me | Theorems.Thm_BorkarMeynODE_Tapering_scaled_moments_bounded
-- name    : BorkarMeynODE.Tapering.scaled_moments_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:44:26.881525+00:00
-- url     : https://prove2.me/theorems/17ebb2b0-a080-4ad0-9922-f63f2fa28cec
-- title:
--   Lemma 4.5 — uniform second moments of the scaled iterates; $\xi$ is an $L^2$-bounded martingale under (TS)
-- statement:
--   Assume (A1) for $(h,h_\infty)$, (A2) with constant $C_0$ for the natural filtration $\{\mathcal F_n\}$ of $X$, step sizes satisfying (TS) or (BS), and fix $T>0$. Let $X$ follow the recursion (1.1) with a random initial condition satisfying $\mathsf E[\|X(0)\|^2]<\infty$. With the blocks $m(j)$, $T(j)$, scales $r(j)$, scaled iterates $\tilde X$, block functions $\phi_j$, and noise sum $\xi$:
--
--   1. $\displaystyle\sup_{n\ge0}\mathsf E\big[\|\tilde X(n)\|^2\big]<\infty$;
--   2. $\displaystyle\sup_{j\ge0}\mathsf E\big[\|X(m(j+1))/r(j)\|^2\big]<\infty$;
--   3. $\displaystyle\sup_{j\ge0,\ T(j)\le t\le T(j+1)}\mathsf E\big[\|\phi_j(t)\|^2\big]<\infty$;
--   4. under (TS), $\{\xi(n),\mathcal F_n\}$ is a square-integrable martingale with
--   $$
--   \sup_{n\ge0}\mathsf E\big[\|\xi(n)\|^2\big]<\infty .
--   $$
--
--   Item 4 gives almost sure convergence of $\xi(n)$ by the martingale convergence theorem, which is how the noise is shown to be negligible in Lemma 4.6.
--
--   **Formalization Note** The suprema of second moments are taken in $[0,\infty]$ (lower Lebesgue integrals of $\|\cdot\|^2$), so "$<\top$" is exactly "$<\infty$" and no real-valued supremum of an unbounded family can occur. In item 3, $\phi_j$ is $\phi$ on $[T(j),T(j+1))$ extended to $T(j+1)$ by its left limit $X(m(j+1))/r(j)$; the page writes $\phi(t)$. Item 4 is stated as an implication from (TS) inside the conclusion, so the lemma carries "(TS) or (BS)" as on the page.
-- source:
--   Borkar and Meyn, The O.D.E. Method for Convergence of Stochastic Approximation and Reinforcement Learning, SIAM J. Control Optim. 38(2) (2000), p. 462, Lemma 4.5 (i)-(iv)

import Mathlib
import Definitions.Def_BorkarMeynODE_Tapering_ODEStability
import Definitions.Def_BorkarMeynODE_Tapering_AssumptionA1
import Definitions.Def_BorkarMeynODE_Tapering_Stepsizes
import Definitions.Def_BorkarMeynODE_Tapering_SAModel
import Definitions.Def_BorkarMeynODE_Tapering_TimeGrid
import Definitions.Def_BorkarMeynODE_Tapering_ScaledInterpolation
import Definitions.Def_BorkarMeynODE_Tapering_ScaledNoise

namespace BorkarMeynODE.Tapering

open MeasureTheory

/-- **Lemma 4.5** (Borkar–Meyn 2000, p. 462). Assume (A1), (A2) with constant `C₀` for the
natural filtration `𝓕` of `X`, step sizes satisfying (TS) or (BS), a block length `T > 0`, and
an initial condition with `E‖X(0)‖² < ∞`. Then
(i) `sup_{n≥0} E‖X̃(n)‖² < ∞`;
(ii) `sup_{j≥0} E‖X(m(j+1))/r(j)‖² < ∞`;
(iii) `sup_{j≥0, T(j)≤t≤T(j+1)} E‖φ_j(t)‖² < ∞`, where `φ_j` is `φ` on `[T(j), T(j+1))`
extended to `T(j+1)` by its left limit `X(m(j+1))/r(j)`;
(iv) under (TS), `(ξ(n), 𝓕_n)` is a square-integrable martingale with
`sup_{n≥0} E‖ξ(n)‖² < ∞`.
The suprema are taken in `[0, ∞]` (lower Lebesgue integrals), so "`< ⊤`" is exactly "`< ∞`". -/
theorem scaled_moments_bounded {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h hInf : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (a : ℕ → ℝ) (C₀ : ℝ)
    (hA1 : AssumptionA1 h hInf) (ha : TaperingStepsize a ∨ BoundedStepsize a)
    (T : ℝ) (hT : 0 < T)
    (X M : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hX : ∀ n, StronglyMeasurable (X n))
    (hrec : IsSARecursion h a X M) (hA2 : AssumptionA2 P X M hX C₀)
    (hX0 : Integrable (fun ω => ‖X 0 ω‖ ^ 2) P) :
    (⨆ n : ℕ, ∫⁻ ω, ‖scaledIterate a T (fun k => X k ω) n‖ₑ ^ 2 ∂P) < ⊤ ∧
    (⨆ j : ℕ, ∫⁻ ω, ‖(blockScale a T (fun k => X k ω) j)⁻¹ •
        X (blockIndex a T (j + 1)) ω‖ₑ ^ 2 ∂P) < ⊤ ∧
    (⨆ j : ℕ, ⨆ t ∈ Set.Icc (blockTime a T j) (blockTime a T (j + 1)),
        ∫⁻ ω, ‖phiBlock a T (fun k => X k ω) j t‖ₑ ^ 2 ∂P) < ⊤ ∧
    (TaperingStepsize a →
      Martingale (fun n ω => noiseSum a T (fun k => X k ω) (fun k => M k ω) n)
        (Filtration.natural X hX) P ∧
      (∀ n, MemLp (fun ω => noiseSum a T (fun k => X k ω) (fun k => M k ω) n) 2 P) ∧
      (⨆ n : ℕ, ∫⁻ ω,
        ‖noiseSum a T (fun k => X k ω) (fun k => M k ω) n‖ₑ ^ 2 ∂P) < ⊤) := by sorry

end BorkarMeynODE.Tapering
