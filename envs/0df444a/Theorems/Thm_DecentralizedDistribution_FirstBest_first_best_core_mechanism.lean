-- Prove2me | Theorems.Thm_DecentralizedDistribution_FirstBest_first_best_core_mechanism
-- name    : DecentralizedDistribution.FirstBest.first_best_core_mechanism
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T07:08:13.099367+00:00
-- url     : https://prove2.me/theorems/8e1255bb-19e5-4d7a-86f9-09978ac32ffd
-- title:
--   Corollary 5.1 — under AR-c the first-best inventory is a Nash equilibrium with allocations in the core
-- statement:
--   Let demand have a probability law $\mu$ under which all demands are nonnegative almost surely, let $\theta_n\in(0,1)$ with $\sum_{n=1}^N\theta_n=1$, and let $[Z]^{c*}$ be a first-best profile (a maximizer of the expected centralized profit $J^c_{\mathcal N}$ over nonnegative profiles). Choose, measurably in $\vec D$, dual prices $(\nu,\gamma,\delta)(\vec D)$ of the grand-coalition shipping LP (6) at $[Z]^{c*}$ for every demand realization, and let $\alpha^d$ be the resulting dual-price allocation (8). Consider the modified fractional allocation rule AR-c,
--   $$\alpha^c_n([Z],\vec D)=\alpha^f_n([Z],\vec D)+w_n([Z]^{c*},\vec D),\qquad w_n([Z]^{c*},\vec D)=\alpha^d_n([Z]^{c*},\vec D)-\alpha^f_n([Z]^{c*},\vec D),$$
--   with $\alpha^f$ the fractional rule (11). Then
--   1. the side payments $w_n([Z]^{c*},\cdot)$ are integrable;
--   2. $[Z]^{c*}$ is a pure-strategy Nash equilibrium (10) of the inventory game under AR-c;
--   3. at $[Z]^{c*}$ the AR-c allocations lie in the core of SAG$([Z]^{c*},\vec D)$ for every demand realization $\vec D$.
--
--   This is the paper's mechanism achieving the first-best: the centrally optimal inventory is an equilibrium of the decentralized stocking game, and the ex-post split of the pooling surplus is stable against every coalition.
--
--   **Formalization Note.** "The NE using $\alpha^c$ is first-best" is stated as "the first-best profile is a Nash equilibrium under AR-c", the direction the paper's proof (Theorem 5.2 followed by Theorem 5.1) gives; uniqueness is the separate Theorem 5.3 and is not claimed. The side payment is the one the proof of Theorem 5.1 constructs, dual allocation minus AR-f allocation at $[Z]^{c*}$. The measurable choice of dual prices is the Lean reading of the paper's "appropriate way of breaking ties in case of degeneracy"; together with almost-sure nonnegative demand it makes all expectations finite. The weights $\gamma_n$ of the paper are written $\theta_n$.
-- source:
--   Anupindi, Bassok & Zemel, A General Framework for the Study of Decentralized Distribution Systems, MSOM 3(4) 2001, p. 361, Corollary 5.1 (with Theorem 5.1, Theorem 5.2 and their proofs, p. 367)

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_DecentralizedDistribution_FirstBest_System
import Definitions.Def_DecentralizedDistribution_FirstBest_DualPrices
import Definitions.Def_DecentralizedDistribution_FirstBest_Game

open MeasureTheory Supermodularity.Cooperative

namespace DecentralizedDistribution.FirstBest

/-- Corollary 5.1 (p. 361). Let demand be a.e. nonnegative, `θ_n ∈ (0, 1)` with `∑_n θ_n = 1`,
`[Z]^{c*}` a first-best profile, and `sel` a measurable choice of optimal dual prices of (6) at
`[Z]^{c*}` for every demand realization. Under the modified fractional rule AR-c
(`α^c = α^f + w`, `w = α^d([Z]^{c*}, ·) - α^f([Z]^{c*}, ·)`): the side payments are integrable,
`[Z]^{c*}` is a pure-strategy Nash equilibrium, and at `[Z]^{c*}` the allocations are in the core
of SAG([Z]^{c*}, D⃗) for every `D⃗`. -/
theorem first_best_core_mechanism {N W : ℕ} (sys : System N W)
    (μ : Measure (Demand N)) [IsProbabilityMeasure μ]
    (hD : ∀ᵐ D ∂μ, ∀ n, 0 ≤ D n)
    (θ : Fin N → ℝ) (hθ : ∀ n, 0 < θ n ∧ θ n < 1) (hθsum : ∑ n, θ n = 1)
    (Zc : Profile N W) (hZc : IsFirstBest sys μ Zc)
    (sel : Demand N → DualPrices N W) (hsel_meas : Measurable sel)
    (hsel_opt : ∀ D, IsOptimalDual sys Zc D (sel D)) :
    (∀ n, Integrable (firstBestSidePayment sys θ Zc sel n) μ) ∧
    IsNashEquilibrium sys μ (coreFractionalRule sys θ Zc sel) Zc ∧
    ∀ D : Demand N,
      (fun n => coreFractionalRule sys θ Zc sel Zc D n)
        ∈ Core Finset.univ (fun S => coalitionValue sys S Zc D) := by sorry

end DecentralizedDistribution.FirstBest
