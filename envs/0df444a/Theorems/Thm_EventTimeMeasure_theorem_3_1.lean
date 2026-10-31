-- Prove2me | Theorems.Thm_EventTimeMeasure_theorem_3_1
-- name    : EventTimeMeasure.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:25:26.300691+00:00
-- url     : https://prove2.me/theorems/de186850-5324-4f6a-af9f-55fd7768a6a9
-- title:
--   Theorem 3.1 (corrected: sequential independence, compensator hypothesis) — $\mathbb Q=Z_\infty P$ is a probability measure and $N$ has $\mathbb Q$-intensity $u^ip^i$
-- statement:
--   **Theorem 3.1 (corrected).** Throughout, $(\Omega,\mathcal F,P)$ is a probability space carrying the event timing model of §2.1: standard exponential thresholds $\xi_1,\dots,\xi_n$, clock filtrations $\mathbb H_i$, nonnegative $\mathbb H_i$-progressive hazard rates $h^i$ with clocks $H^i_t=\int_0^t h^i_s\,ds$ (finite for finite $t$, $H^i_\infty=\infty$), event times $\tau_i=\inf\{t>0: H^i_t\ge\xi_i\}$, indicators $N^i_t=\mathbf 1\{\tau_i\le t\}$, intensities $p^i_s=h^i_s\mathbf 1\{\tau_i>s\}$, and a right-continuous information filtration $\mathbb F\supseteq\mathbb H_i$ making every $\tau_i$ a stopping time. The multiplier $u=(u^1,\dots,u^n)$ has $u^i\ge 0$ $\mathbb H_i$-predictable and locally bounded, $Q^i_t=\int_0^t u^i_s h^i_s\,ds$ (7), and $Z_\infty=\exp\bigl(\sum_i (H^i-Q^i)_{\tau_i}\bigr)\prod_i u^i_{\tau_i}$ (fn 17).
--
--   Assume **sequential independence**: for every $i$, $\xi_i$ is independent under $P$ of $\sigma(\mathcal H^j_\infty: j\le i)\vee\sigma(\xi_j: j<i)$; and the **compensator hypothesis**: for every $i$, $N^i-H^i_{\cdot\wedge\tau_i}$ is an $\mathbb F$-martingale under $P$. Suppose that for every $i$,
--   $$Q^i_\infty=\infty\ \ P\text{-a.s.}\qquad\text{or}\qquad (H^i-Q^i)_\infty<\infty\ \ P\text{-a.s.}$$
--   Then:
--
--   1. $\mathbb Q=Z_\infty P$ is a probability measure;
--   2. $\mathbb Q$ is absolutely continuous with respect to $P$;
--   3. $N$ admits the $\mathbb Q$-intensity $q=(q^1,\dots,q^n)$, $q^i=u^ip^i$: for every $i$,
--   $$N^i_t-\int_0^t q^i_s\,ds=N^i_t-Q^i_{t\wedge\tau_i}$$
--   is an $\mathbb F$-martingale under $\mathbb Q$.
--
--   The theorem is the foundation of the paper's simulation method: changing measure from $P$ to $\mathbb Q$ multiplies every intensity by $u$, and $1/Z_\infty$ is the likelihood ratio that keeps the Monte Carlo estimator unbiased. As printed, with the two independence assumptions of §2.1 and the compensator property asserted as a consequence, the theorem is false; the two hypotheses above are the minimal correction.
--
--   **Formalization Note** The condition $(H^i-Q^i)_\infty<\infty$ is read as $\limsup_{t\to\infty}(H^i_t-Q^i_t)<\infty$ in the extended reals. Clause 3 includes integrability under $\mathbb Q$ at every time, which Mathlib's `Martingale` does not.
--
--   Differences from the source:
--   - correction: §2.1, p.5: the ξ_i are mutually independent and each 𝓗^i_∞ is independent of σ(ξ_i) → hypothesis M.SeqIndep: for every i, ξ_i is independent under P of σ(𝓗^j_∞ : j ≤ i) ∨ σ(ξ_j : j < i); it implies both printed assumptions and equals them for n = 1; reason: as printed, Theorem 3.1 is false: counterexample B (n = 2, h^1 = h^2 ≡ 1, ℍ_1 and ℍ_2 the natural filtrations of N^2 and N^1, u^1_t = e^{−t} for t ≤ τ_2 and 1 after, u^2 symmetric) satisfies every printed assumption, has Q^i_∞ = ∞, and gives E(Z_∞) = 1 − e^{−2} < 1; sequential independence is exactly what the induction step (Appendix A, pp.28–29) uses
--   - correction: §2.1, p.5: M^i = N^i − A^i with A^i_s = H^i_{s∧τ_i} is a martingale, asserted as a consequence of the setting → hypothesis M.CompensatorMartingale: N^i − H^i_{·∧τ_i} is an integrable 𝔽-martingale under P; reason: the assertion does not follow: counterexample A (n = 2, h ≡ 1, ℍ_1 ≡ σ(1{ξ_2 ≥ 1}), ℍ_2 ≡ σ(1{ξ_1 ≥ 1}), u^1 = c(ξ_2), u^2 = c(ξ_1) with c = 1 on [0,1) and 2 on [1,∞)) satisfies §2.1, but the 𝔽-compensator of N^i is not H^i_{·∧τ_i} and E(Z_∞) = 1 + e^{−2}(1 − e^{−1})² > 1
--   - generalization: 𝔽 is the progressive enlargement of ℍ_1 ∨ ⋯ ∨ ℍ_n by the τ_i (fn 7, p.5); the probability space and the filtrations are complete; the τ_i are totally inaccessible → 𝔽 is any right-continuous filtration containing every ℍ_i for which every τ_i is a stopping time; completeness, total inaccessibility and almost-sure distinctness of the τ_i are not assumed; n = 0 is allowed; reason: the progressive enlargement is such a filtration, so the statement specializes to the source's; total inaccessibility is implied by the continuous compensator of M.CompensatorMartingale, and distinctness by sequential independence (for i < j the atomless ξ_j is independent of H^j_{τ_i}); at n = 0 the density is 1 and the statement is the trivial case
--   - reading: §3, p.9: u^i is nonnegative, ℍ_i-predictable and locally bounded (the filtration of the localization is not named) → IsMultiplier: u^i is ℍ_i-predictable (Mathlib IsStronglyPredictable) and locally bounded along a localizing sequence of 𝔽-stopping times (Mathlib Locally); reason: the weaker hypothesis of the two readings: localization in ℍ_i implies localization in 𝔽, since ℍ_i ⊆ 𝔽
--   - reading: Theorem 3.1, p.9: (H^i − Q^i)_∞ < ∞ P-almost surely → limsup_{t→∞} (H^i_t − Q^i_t) < ∞ P-almost surely, the limsup taken in EReal; reason: the limit need not exist and the limsup reading is the weakest hypothesis; given H^i_∞ = ∞ it implies Q^i_∞ = ∞, so every reading of the disjunction is the same condition
--   - encoding: time [0, ∞); H^i continuous, increasing, H^i_0 = 0, H^i_t = ∫_0^t h^i_s ds (3); τ_i = inf{t > 0 : H^i_t ≥ ξ_i} (2) → time ℝ≥0; H^i_t is the lower Lebesgue integral of h^i over [0, t] in ℝ≥0∞ for t ∈ [0, ∞], finite at finite t almost surely; τ_i takes values in [0, ∞] = WithTop ℝ≥0 with inf ∅ = ∞; reason: Lean convention; continuity, monotonicity and H^i_0 = 0 follow from the integral form (3), and no instance changes
--   - encoding: Z_∞ = L_∞^{−1} with L_∞ = exp(∑_i (Q^i − H^i)_{τ_i} − log u^i_{τ_i}) (9), convention 1/0 = ∞ (fn 17) → Z_∞ = exp(∑_i (H^i − Q^i)_{τ_i}) ∏_i u^i_{τ_i} on {every τ_i < ∞}, and 1 on the P-null complement; ℚ = P.withDensity Z_∞; reason: same value wherever the source's expression is defined (a factor u^i_{τ_i} = 0 gives 0, as 1/∞ = 0); the exceptional event is P-null because H^i_∞ = ∞
--   - encoding: N admits the ℚ-intensity q^i = u^i p^i: N^i − ∫_0^· q^i_s ds is a ℚ-martingale (p.9) → Mathlib Martingale of t ↦ N^i_t − Q^i_{t∧τ_i} for 𝔽 under ℚ, together with integrability under ℚ at every t; reason: ∫_0^t q^i_s ds = Q^i_{t∧τ_i} because p^i_s = h^i_s 1{s < τ_i}; Mathlib's Martingale omits the integrability that the usual definition includes
-- source:
--   Giesecke–Shkolnik, Reducing Bias in Event Time Simulations via Measure Changes, authors' manuscript of January 16, 2018 (Math. Oper. Res., doi:10.1287/moor.2021.1156), Theorem 3.1, p.9

import Mathlib
import Definitions.Def_EventTimeMeasure_Model
import Definitions.Def_EventTimeMeasure_MeasureChange

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace EventTimeMeasure

/-- **Theorem 3.1 (corrected)** (Giesecke–Shkolnik, *Reducing Bias in Event Time Simulations via
Measure Changes*, manuscript of January 16, 2018, Theorem 3.1, p.9). In the event timing model of
§2.1 with sequential independence (`M.SeqIndep`) and with each `N^i − H^i_{· ∧ τ_i}` an
`𝔽`-martingale (`M.CompensatorMartingale`), let `u` be nonnegative, `ℍ_i`-predictable and
locally bounded. Suppose that for every `i`, either `Q^i_∞ = ∞` `P`-a.s. or `(H^i − Q^i)_∞ < ∞`
`P`-a.s. Then `ℚ = Z_∞ P` is a probability measure, absolutely continuous with respect to `P`,
and `N` admits the `ℚ`-intensity `q^i = u^i p^i`: for every `i`, `N^i − ∫_0^· q^i_s ds =
N^i − Q^i_{· ∧ τ_i}` is an integrable `𝔽`-martingale under `ℚ`.

**Formalization Note** Corrections (see the item's `Differences from the source`): the printed
independence assumptions of §2.1 are replaced by `M.SeqIndep`, and the `𝔽`-martingale property of
`N^i − H^i_{·∧τ_i}`, asserted on p.5, is a hypothesis. `(H^i − Q^i)_∞ < ∞` is read as
`limsup_{t→∞} (H^i_t − Q^i_t) < ∞` in `EReal`. `∫_0^t q^i_s ds = Q^i_{t ∧ τ_i}` since
`q^i_s = u^i_s h^i_s 1{s < τ_i}`. Mathlib's `Martingale` does not include integrability, which is
stated separately. -/
theorem theorem_3_1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (M : Model P n) (u : Fin n → ℝ≥0 → Ω → ℝ≥0) (hu : M.IsMultiplier u)
    (hseq : M.SeqIndep) (hcomp : M.CompensatorMartingale)
    (hcond : ∀ i, (∀ᵐ ω ∂P, M.Qc u i ⊤ ω = ⊤) ∨
      (∀ᵐ ω ∂P, limsup (fun t : ℝ≥0 ↦
        (((M.H i t ω).toReal - (M.Qc u i t ω).toReal : ℝ) : EReal)) atTop < ⊤)) :
    IsProbabilityMeasure (M.simMeasure u) ∧ M.simMeasure u ≪ P ∧
      ∀ i : Fin n,
        Martingale (fun t ω ↦ M.N i t ω - (M.Qc u i (min (t : WithTop ℝ≥0) (M.τ i ω)) ω).toReal)
          M.𝓕 (M.simMeasure u) ∧
        ∀ t : ℝ≥0, Integrable
          (fun ω ↦ M.N i t ω - (M.Qc u i (min (t : WithTop ℝ≥0) (M.τ i ω)) ω).toReal)
          (M.simMeasure u) := by sorry

end EventTimeMeasure
