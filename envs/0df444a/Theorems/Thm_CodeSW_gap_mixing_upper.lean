-- Prove2me | Theorems.Thm_CodeSW_gap_mixing_upper
-- name    : CodeSW.gap_mixing_upper
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:23:37.604705+00:00
-- url     : https://prove2.me/theorems/d83cb8da-da39-4487-b876-92ae51f58344
-- title:
--   Appendix A display, p.33, upper half — $\tau(P)\le\log\bigl(2e/\min_S p(S)\bigr)\Delta(P)^{-1}$
-- statement:
--   **Mixing from the absolute spectral gap.** Let $P$ be an irreducible, aperiodic Markov chain on a finite state space, reversible with respect to its stationary distribution $p$, and let $\Delta(P)=1-\max\{|\lambda|:\lambda\text{ an eigenvalue of }P,\ \lambda\ne1\}$. For every integer $t$ with
--   $$t\ge\log\Bigl(\frac{2e}{\min_S p(S)}\Bigr)\Delta(P)^{-1},$$
--   one has $\max_x\|P^t(x,\cdot)-p\|_{\mathrm{TV}}\le 1/(2e)$. That is, the mixing time $\tau(P)$ with $\ell^1$ threshold $e^{-1}$ is at most $\log(2e/\min_S p(S))\Delta(P)^{-1}$, with no additive $+1$.
--
--   This is the half of the spectral characterization of mixing time that converts congestion bounds into mixing bounds.
--
--   Differences from the source:
--   - reading: the display states no hypotheses on P and cites [LPW09, Theorems 12.3 & 12.4] → P stochastic, irreducible, aperiodic and reversible for p; reason: this is the setting of the cited theorems
--   - encoding: τ(P) = min_t[max_x ∑_y |P^t(x,y) − p(y)| ≤ e^{−1}] ≤ T → for all t ≥ T, distStationary P p t ≤ 1/(2e); reason: total variation is half the ℓ¹ distance and d(t) is non-increasing; this also avoids the junk value of an empty sInf
-- source:
--   Hangleiter, Ju, Vazirani, Code Swendsen-Wang Dynamics, arXiv:2510.08446 (manuscript sha256 4e4abb5e…), Appendix A, display on p.33

import Definitions.Def_mm_spectral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Matrix

namespace CodeSW

/-- **Spectral gap and mixing time, upper half** (display of Appendix A, p.33, after [LPW09,
Theorems 12.3 & 12.4]): `τ(P) ≤ log(2e / min_{S∈Ω} p(S)) ∆(P)^{−1}`, where
`∆(P) = 1 − max{|λ| : λ an eigenvalue of P, λ ≠ 1}` is the absolute spectral gap. Stated for a
reversible, irreducible, aperiodic chain `P` with stationary law `p`: after any
`t ≥ log(2e/p_min)·∆(P)^{−1}` steps the chain is within total variation `1/(2e)` of `p` from
every start (Hangleiter, Ju, Vazirani, *Code Swendsen-Wang Dynamics*, arXiv:2510.08446,
manuscript sha256 4e4abb5e…, Appendix A, display on p.33).

**Formalization Note** `∆(P)^{−1}` is `MarkovMixing.relaxationTime P = 1/absSpectralGap P`; the
threshold `e^{−1}` on `∑_y |P^t(x,y) − p(y)|` is total variation `1/(2e)`; "`τ ≤ T`" is the bound
for every `t ≥ T`. There is no `+1`, unlike the published
`MarkovMixing.relaxation_upper_aperiodic`, which this statement strengthens at `ε = 1/(2e)`. -/
theorem gap_mixing_upper {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (P : Matrix Ω Ω ℝ)
    (hP : MarkovMixing.IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (hap : MarkovMixing.Aperiodic P) (p : Ω → ℝ) (hp : MarkovMixing.IsStationary P p)
    (hrev : MarkovMixing.DetailedBalance P p) (t : ℕ)
    (ht : Real.log (2 * Real.exp 1 / ⨅ S, p S) * MarkovMixing.relaxationTime P ≤ (t : ℝ)) :
    MarkovMixing.distStationary P p t ≤ 1 / (2 * Real.exp 1) := by sorry

end CodeSW
