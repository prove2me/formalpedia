-- Prove2me | Theorems.Thm_EventTimeMeasure_eq_42
-- name    : EventTimeMeasure.eq_42
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:25:28.690527+00:00
-- url     : https://prove2.me/theorems/beb2a33d-4445-4d8e-b164-a68f0f28813e
-- title:
--   (42), p.28 (corrected: hypotheses of Theorem 3.1) — $\limsup_{k}\mathbf E_{\mathbb Q_\ell}(Z_{\theta_k}\mathbf 1\{Z_{\theta_k}>e^z\})\to0$ as $z\uparrow\infty$
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space carrying the event timing model of §2.1: standard exponential thresholds $\xi_1,\dots,\xi_n$, clock filtrations $\mathbb H_i$, nonnegative $\mathbb H_i$-progressive hazard rates $h^i$ with clocks $H^i_t=\int_0^t h^i_s\,ds$ (finite for finite $t$, $H^i_\infty=\infty$), event times $\tau_i=\inf\{t>0: H^i_t\ge\xi_i\}$, indicators $N^i_t=\mathbf 1\{\tau_i\le t\}$, intensities $p^i_s=h^i_s\mathbf 1\{\tau_i>s\}$, and a right-continuous information filtration $\mathbb F\supseteq\mathbb H_i$ making every $\tau_i$ a stopping time. The multiplier $u=(u^1,\dots,u^n)$ has $u^i\ge 0$ $\mathbb H_i$-predictable and locally bounded, $Q^i_t=\int_0^t u^i_s h^i_s\,ds$ (7), and $Z_\infty=\exp\bigl(\sum_i (H^i-Q^i)_{\tau_i}\bigr)\prod_i u^i_{\tau_i}$ (fn 17).
--
--   The hypotheses are those of the corrected Theorem 3.1: **sequential independence** (each $\xi_i$ is independent of $\sigma(\mathcal H^j_\infty: j\le i)\vee\sigma(\xi_j: j<i)$), the **compensator hypothesis** ($N^i-H^i_{\cdot\wedge\tau_i}$ is an $\mathbb F$-martingale under $P$), and, for every $i$, $Q^i_\infty=\infty$ a.s. or $\limsup_{t\to\infty}(H^i_t-Q^i_t)<\infty$ a.s.
--
--   At the induction step of Appendix A the events $1,\dots,\ell$ are already tilted: $\mathbb Q_\ell=Z^\ell_\infty P$, where $Z^\ell_\infty$ is $Z_\infty$ with $u^i=1$ for $i>\ell$. For the next event (index $\ell+1$, whose sub- and superscripts the paper drops) let
--   $$Z_t=\exp\Bigl(\int_0^t(1-u_s)p_s\,ds+N_t\log u_\tau\Bigr)=e^{(H-Q)_{t\wedge\tau}}\,\bigl(u_\tau\ \text{if}\ \tau\le t,\ \text{else } 1\bigr),\qquad 0\le t\le\infty,$$
--   $Z_{s-}$ its left limit, and $\theta_k=\inf\{t\ge 0:\int_0^t(1+u_s)h_s\,ds\ge k\}$ (40), $k\in\mathbb N$.
--
--   Then
--   $$\limsup_{k\uparrow\infty}\mathbf E_{\mathbb Q_\ell}\bigl(Z_{\theta_k}\mathbf 1\{Z_{\theta_k}>e^z\}\bigr)\to0\qquad(z\uparrow\infty).\qquad(42)$$
--
--   This tail bound, together with $\mathbf E_{\mathbb Q_\ell}(Z_{\theta_k}\mathbf 1_A)\le1$, gives the uniform integrability of $\{Z_{\theta_k}\}_k$ under $\mathbb Q_\ell$.
--
--   **Formalization Note** The expectation is a lower Lebesgue integral and $z$ ranges over $\mathbb R$; the conclusion is the convergence of the function $z\mapsto\limsup_k(\cdot)$ to $0$ as $z\to\infty$.
--
--   Differences from the source:
--   - correction: §2.1, p.5: the ξ_i are mutually independent and each 𝓗^i_∞ is independent of σ(ξ_i) → hypothesis M.SeqIndep: for every i, ξ_i is independent under P of σ(𝓗^j_∞ : j ≤ i) ∨ σ(ξ_j : j < i); it implies both printed assumptions and equals them for n = 1; reason: as printed, Theorem 3.1 is false: counterexample B (n = 2, h^1 = h^2 ≡ 1, ℍ_1 and ℍ_2 the natural filtrations of N^2 and N^1, u^1_t = e^{−t} for t ≤ τ_2 and 1 after, u^2 symmetric) satisfies every printed assumption, has Q^i_∞ = ∞, and gives E(Z_∞) = 1 − e^{−2} < 1; sequential independence is exactly what the induction step (Appendix A, pp.28–29) uses
--   - correction: §2.1, p.5: M^i = N^i − A^i with A^i_s = H^i_{s∧τ_i} is a martingale, asserted as a consequence of the setting → hypothesis M.CompensatorMartingale: N^i − H^i_{·∧τ_i} is an integrable 𝔽-martingale under P; reason: the assertion does not follow: counterexample A (n = 2, h ≡ 1, ℍ_1 ≡ σ(1{ξ_2 ≥ 1}), ℍ_2 ≡ σ(1{ξ_1 ≥ 1}), u^1 = c(ξ_2), u^2 = c(ξ_1) with c = 1 on [0,1) and 2 on [1,∞)) satisfies §2.1, but the 𝔽-compensator of N^i is not H^i_{·∧τ_i} and E(Z_∞) = 1 + e^{−2}(1 − e^{−1})² > 1
--   - generalization: 𝔽 is the progressive enlargement of ℍ_1 ∨ ⋯ ∨ ℍ_n by the τ_i (fn 7, p.5); the probability space and the filtrations are complete; the τ_i are totally inaccessible → 𝔽 is any right-continuous filtration containing every ℍ_i for which every τ_i is a stopping time; completeness, total inaccessibility and almost-sure distinctness of the τ_i are not assumed; n = 0 is allowed; reason: the progressive enlargement is such a filtration, so the statement specializes to the source's; total inaccessibility is implied by the continuous compensator of M.CompensatorMartingale, and distinctness by sequential independence (for i < j the atomless ξ_j is independent of H^j_{τ_i}); at n = 0 the density is 1 and the statement is the trivial case
--   - reading: §3, p.9: u^i is nonnegative, ℍ_i-predictable and locally bounded (the filtration of the localization is not named) → IsMultiplier: u^i is ℍ_i-predictable (Mathlib IsStronglyPredictable) and locally bounded along a localizing sequence of 𝔽-stopping times (Mathlib Locally); reason: the weaker hypothesis of the two readings: localization in ℍ_i implies localization in 𝔽, since ℍ_i ⊆ 𝔽
--   - reading: Theorem 3.1, p.9: (H^i − Q^i)_∞ < ∞ P-almost surely → limsup_{t→∞} (H^i_t − Q^i_t) < ∞ P-almost surely, the limsup taken in EReal; reason: the limit need not exist and the limsup reading is the weakest hypothesis; given H^i_∞ = ∞ it implies Q^i_∞ = ∞, so every reading of the disjunction is the same condition
--   - encoding: time [0, ∞); H^i continuous, increasing, H^i_0 = 0, H^i_t = ∫_0^t h^i_s ds (3); τ_i = inf{t > 0 : H^i_t ≥ ξ_i} (2) → time ℝ≥0; H^i_t is the lower Lebesgue integral of h^i over [0, t] in ℝ≥0∞ for t ∈ [0, ∞], finite at finite t almost surely; τ_i takes values in [0, ∞] = WithTop ℝ≥0 with inf ∅ = ∞; reason: Lean convention; continuity, monotonicity and H^i_0 = 0 follow from the integral form (3), and no instance changes
--   - encoding: Z_t = exp(∫_0^t (1 − u_s) p_s ds + N_t log(u_τ)) for the event ℓ + 1, with Z_{s−} its left limit (p.27) → zProc: exp((H − Q)_{t∧τ}) · (u_τ if τ ≤ t, else 1) for t ∈ [0, ∞]; zProcLeft: the same with τ < s; ℚ_ℓ = Z^ℓ_∞ P is simMeasure (uBefore u ℓ); on the P-null event {τ = ∞}, u_τ is read as u_0; reason: ∫_0^t (1 − u_s) p_s ds = (H − Q)_{t∧τ}; the factor form is exp(N_t log u_τ) with log 0 = −∞, and t ↦ (H − Q)_{t∧τ} is continuous, so zProcLeft is the left limit; {τ = ∞} is also ℚ_ℓ-null, since ℚ_ℓ ≪ P
--   - encoding: θ_k = inf{t ≥ 0 : ∫_0^t (1 + u_s) h_s ds ≥ k} (40), k ∈ ℕ → theta: the infimum in [0, ∞] = WithTop ℝ≥0 (∞ when the integral never reaches k), with the integral a lower Lebesgue integral; reason: Lean convention; θ_k < ∞ almost surely because H_∞ = ∞
--   - generalization: stated inside the induction of Appendix A for ℓ = 0, 1, …, n − 1 → stated for every event j : Fin n (the paper's ℓ + 1 with ℓ = j) under the hypotheses of the corrected Theorem 3.1, with no induction hypothesis assumed; reason: the source's induction step is the case of each ℓ; the statements carry no hidden induction hypothesis
--   - encoding: Z_∞ = L_∞^{−1} with L_∞ = exp(∑_i (Q^i − H^i)_{τ_i} − log u^i_{τ_i}) (9), convention 1/0 = ∞ (fn 17) → Z_∞ = exp(∑_i (H^i − Q^i)_{τ_i}) ∏_i u^i_{τ_i} on {every τ_i < ∞}, and 1 on the P-null complement; ℚ = P.withDensity Z_∞; reason: same value wherever the source's expression is defined (a factor u^i_{τ_i} = 0 gives 0, as 1/∞ = 0); the exceptional event is P-null because H^i_∞ = ∞
-- source:
--   Giesecke–Shkolnik, Reducing Bias in Event Time Simulations via Measure Changes, authors' manuscript of January 16, 2018 (Math. Oper. Res., doi:10.1287/moor.2021.1156), Appendix A, eq. (42), p.28

import Mathlib
import Definitions.Def_EventTimeMeasure_Model
import Definitions.Def_EventTimeMeasure_MeasureChange

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace EventTimeMeasure

/-- **Uniform tail bound, eq. (42)** (Giesecke–Shkolnik, *Reducing Bias in Event Time
Simulations via Measure Changes*, manuscript of January 16, 2018, Appendix A, eq. (42), p.28):
`limsup_{k↑∞} E_{ℚ_ℓ}(Z_{θ_k} 1{Z_{θ_k} > e^z}) → 0` as `z ↑ ∞`.

All hypotheses of the corrected Theorem 3.1 (`theorem_3_1`) are assumed; `j : Fin n` is the
event added at the induction step (the paper's `ℓ + 1`, with `ℓ = j` events already tilted), and
`ℚ_ℓ = Z^ℓ_∞ P` is `M.simMeasure (Model.uBefore u j)`.

**Formalization Note** The expectation is a lower Lebesgue integral; `z` ranges over `ℝ`. -/
theorem eq_42 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (M : Model P n) (u : Fin n → ℝ≥0 → Ω → ℝ≥0) (hu : M.IsMultiplier u)
    (hseq : M.SeqIndep) (hcomp : M.CompensatorMartingale)
    (hcond : ∀ i, (∀ᵐ ω ∂P, M.Qc u i ⊤ ω = ⊤) ∨
      (∀ᵐ ω ∂P, limsup (fun t : ℝ≥0 ↦
        (((M.H i t ω).toReal - (M.Qc u i t ω).toReal : ℝ) : EReal)) atTop < ⊤))
    (j : Fin n) :
    Tendsto (fun z : ℝ ↦ limsup (fun k : ℕ ↦ ∫⁻ ω,
        {ω' | Real.exp z < M.zProc u j (M.theta u j k ω') ω'}.indicator
          (fun ω' ↦ ENNReal.ofReal (M.zProc u j (M.theta u j k ω') ω')) ω
        ∂(M.simMeasure (Model.uBefore u j))) atTop) atTop (𝓝 0) := by sorry

end EventTimeMeasure
