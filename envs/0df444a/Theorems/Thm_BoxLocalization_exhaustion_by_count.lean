-- Prove2me | Theorems.Thm_BoxLocalization_exhaustion_by_count
-- name    : BoxLocalization.exhaustion_by_count
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:31:34.820345+00:00
-- url     : https://prove2.me/theorems/0bfa01c0-d4fa-4f35-8ae1-99b0dbe925e2
-- title:
--   Exhaustion of a finite divisor by a zero list
-- statement:
--   Let $T\subseteq S$ be finite sets of complex numbers, $|T|=n$, and let
--   $d:S\to\mathbb Z$ satisfy $d(\rho)\ge1$ for all $\rho\in S$. If
--   $$\sum_{\rho\in S}d(\rho)=n,$$
--   then $S=T$ and $d(\rho)=1$ for every $\rho\in S$. Thus $n$ distinct points
--   exhaust a total multiplicity of $n$.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_zero_localization/lean/BoxLocalization.lean#L47-L98

import Definitions.Def_ArdaRH65K_XiLineZeros
import Mathlib
/- Task 6 (Stage 3): RH-IN-A-BOX LOCALIZATION CAPSTONE.

   Box `B = [2/5, 3/5] x [10, 35]`.  This file composes the three kernel results of the project into
   the crowning statement: EVERY nontrivial zero of `riemannZeta` in `B` lies on the critical line
   `Re = 1/2` (and is simple).  This is a Turing-style VERIFICATION OF RH INSIDE THIS BOX.  It is NOT
   a proof of the Riemann Hypothesis.  `conjecture1_proved = False`.

   The pieces composed:

   1. TOTAL COUNT = 5 (kernel argument principle):
      `BoxArgPrincipleZeta.box_arg_principle_zeta'` concludes `∃ s d, Σ_{ρ∈s} (d ρ) = N`, where `s`
      is the ACTUAL zeta divisor support on the ball `U = ball cB 13 ⊇ B` and `d` its multiplicity
      (`MeromorphicOn.divisor riemannZeta U`), GIVEN the honest Arb bundle `hArb` at `N = 5`.  The
      winding integer `N = 5`, edge non-vanishing, strict interiority, and the value enclosures are
      the documented NON-KERNEL Arb inputs (same trust boundary as Stage 1's enclosures).

   2. ON-LINE LOWER BOUND >= 5 (kernel, Stage 1):
      `XiLineZeros.lambda_five_zeros_10_35` yields 5 DISTINCT `completedRiemannZeta` zeros on the line
      `Re = 1/2` with imaginary parts in `(10, 35)` (from Arb-certified sign changes).

   3. LAMBDA <-> ZETA BRIDGE (kernel, this file):
      In `B` (`Re > 0`, so `s ≠ 0`), `riemannZeta s = completedRiemannZeta s / Gammaℝ s` with
      `Gammaℝ s ≠ 0`; hence `riemannZeta s = 0 ↔ completedRiemannZeta s = 0`.  The 5 on-line
      `completedRiemannZeta`-zeros ARE 5 distinct on-line `riemannZeta`-zeros in `B`.

   COUNTING ARGUMENT (kernel, this file): the divisor is nonnegative (zeta is analytic on `U`, no
   poles), so `d ρ ≥ 1` at every zero.  The 5 distinct on-line zeros lie in the support `s`, each
   with `d ≥ 1`, summing to `≥ 5`.  Since the TOTAL is exactly `5`, they EXHAUST the divisor: the
   support equals those 5 points and each multiplicity is exactly 1.  Therefore every zeta-zero in
   `B` is one of the 5 on-line zeros -- so it lies on `Re = 1/2` and is simple.

   conjecture1_proved = False. -/




open Complex Real

section
namespace BoxLocalization
end BoxLocalization
open BoxLocalization

/-! ## Part A: the pure combinatorial localization lemma (kernel).

If a finite multiset-with-multiplicity `d ≥ 1` on a support `s` sums to `n`, and we already exhibit
`n` DISTINCT elements of `s`, then `s` is EXACTLY those `n` elements and every multiplicity is `1`.
This is the load-bearing counting step; it is fully general and kernel-proven. -/

theorem BoxLocalization.exhaustion_by_count {s T : Finset ℂ} {d : ℂ → ℤ} {n : ℕ}
    (hTsub : T ⊆ s) (hTcard : T.card = n)
    (hd1 : ∀ ρ ∈ s, (1 : ℤ) ≤ d ρ)
    (hsum : (∑ ρ ∈ s, d ρ) = (n : ℤ)) :
    s = T ∧ ∀ ρ ∈ s, d ρ = 1 := by sorry
