-- Prove2me | Theorems.Thm_EmpiricalDRO_Coverage_eq68_expansion
-- name    : EmpiricalDRO.Coverage.eq68_expansion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T15:09:19.234231+00:00
-- url     : https://prove2.me/theorems/9a48a7ba-3c36-4061-8d97-697d4e3b4460
-- title:
--   (68), p. 30 — −2 log R(x;Z0) = n s⁻¹ h̄² + ε₁ with ε₁ = o_p(1)
-- statement:
--   Let $\xi_1,\xi_2,\dots$ be i.i.d. random elements of a measurable space $\Xi$ under a probability measure $P$, fix a decision $x$ and a measurable function $h(x;\cdot):\Xi\to\mathbb R$ with $\mathbb E\,h(x;\xi)^2<\infty$ and $0<\operatorname{Var}h(x;\xi)$. Let $Z_0(x)=\mathbb E\,h(x;\xi)$, $\tilde h_i=h(x;\xi_i)-Z_0(x)$,
--   $$
--   \bar h=\frac1n\sum_{i=1}^n\tilde h_i,\qquad s=\frac1n\sum_{i=1}^n\tilde h_i^2,
--   $$
--   and let $-2\log R(x;Z_0)$ be the empirical-likelihood statistic of the sample $h(x;\xi_1),\dots,h(x;\xi_n)$ at the value $Z_0(x)$. Then
--   $$
--   -2\log R(x;Z_0)=n\,s^{-1}\bar h^2+\epsilon_1,\qquad \epsilon_1=o_p(1),
--   $$
--   in the sense that for every $\varepsilon>0$
--   $$
--   P\Big(-2\log R(x;Z_0)=\infty\ \text{ or }\ \big|-2\log R(x;Z_0)-n\bar h^2/s\big|>\varepsilon\Big)\longrightarrow0 .
--   $$
--
--   Since $\sqrt n\,\bar h$ is asymptotically normal and $s$ tends to the variance, this expansion yields the $\chi^2_1$ limit of the empirical likelihood theorem.
--
--   **Formalization Note.** Specialised to a single decision point $x$ ($\Theta=\{x\}$), where the paper's Assumptions 1–4 reduce to finite second moment and positive variance and $\|\cdot\|_\Theta$ becomes an absolute value. The event that the statistic is infinite (no feasible weights) is included in the exceptional event; the paper derives (68) on the event where (47) is feasible, whose probability tends to $1$. If $s=0$ Lean's division returns $0$; then every $\tilde h_i=0$ and the statistic is also $0$, so no spurious value enters. Probabilities of events are outer probabilities; no measurability of the events is assumed (the paper sets measurability aside, p. 14).
-- source:
--   Lam, Recovering Best Statistical Guarantees via the Empirical DRO, arXiv:1605.09349v1, p. 30, proof of Theorem 5, (68)

import Mathlib
import Definitions.Def_EmpiricalDRO_Coverage_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace EmpiricalDRO.Coverage

/-- (68), Lam, arXiv:1605.09349v1, p. 30, for one decision point `x` (Θ = {x}): with
`h̃ᵢ = h(x;ξᵢ) − Z0(x)`, `h̄ = (1/n) ∑ h̃ᵢ` and `s = (1/n) ∑ h̃ᵢ²`,
`−2 log R(x;Z0) = n s⁻¹ h̄² + ε₁` with `ε₁ = o_p(1)`: the probability that `−2 log R(x;Z0)` is
infinite or differs from `n h̄²/s` by more than `ε` tends to `0`. -/
theorem eq68_expansion {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ] (ξ : ℕ → Ω → Ξ) (hξ : ∀ i, Measurable (ξ i))
    (hindep : iIndepFun ξ P) (hident : ∀ i, IdentDistrib (ξ i) (ξ 0) P P)
    {m : ℕ} (h : EuclideanSpace ℝ (Fin m) → Ξ → ℝ) (x : EuclideanSpace ℝ (Fin m))
    (hhx : Measurable (h x)) (hL2 : MemLp (fun ω => h x (ξ 0 ω)) 2 P)
    (hvar : 0 < variance (fun ω => h x (ξ 0 ω)) P) :
    let Z0 : ℝ := ∫ ω, h x (ξ 0 ω) ∂P
    let hbar : ℕ → Ω → ℝ := fun n ω => (1 / (n : ℝ)) * ∑ i : Fin n, (h x (ξ i ω) - Z0)
    let s : ℕ → Ω → ℝ := fun n ω => (1 / (n : ℝ)) * ∑ i : Fin n, (h x (ξ i ω) - Z0) ^ 2
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => P {ω |
      ¬ (elStat (fun i : Fin n => h x (ξ i ω)) Z0 ≠ ⊤ ∧
        |(elStat (fun i : Fin n => h x (ξ i ω)) Z0).toReal - n * hbar n ω ^ 2 / s n ω| ≤ ε)})
      atTop (𝓝 0) := by sorry

end EmpiricalDRO.Coverage
