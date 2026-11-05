-- Prove2me | Theorems.Thm_BauerleRiederMDP_Contracting_lemma_7_1_4
-- name    : BauerleRiederMDP.Contracting.lemma_7_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:28:26.452241+00:00
-- url     : https://prove2.me/theorems/dd165018-e3f3-4e9d-94d2-cd7b4da554ae
-- title:
--   Lemma 7.1.4 — weak monotonicity of the finite-horizon values, $J_n\le J_m+\mathcal T_\circ^m\delta$ for $n\ge m$
-- statement:
--   Let $(E,A,D,Q,r,\beta)$ be a stationary Markov Decision Model with infinite horizon, $\beta\in(0,1]$, satisfying the Integrability Assumption (A) and the Convergence Assumption (C). For a Markov policy $\pi=(f_0,f_1,\dots)\in F^\infty$ let
--
--   $$J_{n\pi}=\mathcal T_{f_0}\cdots\mathcal T_{f_{n-1}}0,\qquad J_n=\sup_\pi J_{n\pi},$$
--
--   where $\mathcal T_f v(x)=r(x,f(x))+\beta\int v(x')Q(dx'\mid x,f(x))$. Let $\delta(x)=\sup_\pi\mathbb E^\pi_x\big[\sum_{k\ge0}\beta^kr^+(X_k,f_k(X_k))\big]$ and $\mathcal T_\circ v(x)=\sup_{a\in D(x)}\beta\int v(x')Q(dx'\mid x,a)$. Then for all $n,m\in\mathbb N_0$ with $n\ge m$:
--
--   1. $J_{n\pi}\le J_{m\pi}+\mathcal T_\circ^m\delta$ for every policy $\pi\in F^\infty$;
--   2. $J_n\le J_m+\mathcal T_\circ^m\delta$.
--
--   Combined with (C), the lemma shows that $(J_{n\pi})$ and $(J_n)$ are weakly decreasing, so their limits exist; this is how the limit value function $J=\lim_n J_n$ is defined.
--
--   **Formalization Note** All objects are the published `MDPFinance.Contracting` bundles. Values lie in $[-\infty,\infty)$ and are computed in `EReal`, with $\int v=\int v^+-\int v^-$. The integral of $\delta$ in $\mathcal T_\circ$ is Mathlib's Lebesgue integral, which for a non-measurable $\delta$ is the lower integral.
--
--   Differences from the source:
--   - encoding: Q a stochastic kernel from D to E and r : D → ℝ → Q a Markov kernel on E × A and r measurable on E × A; reason: only values on D enter any statement, and every kernel and reward on D extend to E × A.
--   - encoding: J_{nπ} = T_{f_0}⋯T_{f_{n−1}}0 with [−∞,∞)-valued integrals → EReal recursion with ∫v⁺ − ∫v⁻; reason: this is the book's integral; under (A) every positive part is finite, so no ∞ − ∞ arises.
--   - reading: T_∘δ, defined "whenever the integral exists" → the Lebesgue (lower) integral of δ, also when δ is not measurable; reason: δ need not be measurable (p.197); the integral is the book's whenever δ is measurable.
--   - encoding: δ(x) = sup_π 𝔼^π_x[Σ_k β^k r⁺] → sup_π limsup_n of the n-stage expectations of β^k r⁺; reason: the partial sums are nondecreasing, so the limsup is the full expectation (monotone convergence).
--   - encoding: the tail expectation in (C) → full-horizon minus n-stage expectation of β^k r⁺; reason: both are finite under (A), and the difference is the tail.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Springer Universitext, DOI 10.1007/978-3-642-18324-9, Lemma 7.1.4, p.197 (PDF p.208); standing assumptions (A), (C) and T_∘, p.195 (PDF p.206)

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Value
import Definitions.Def_BauerleRiederMDP_Contracting_ConvergenceAssumptionC

open MeasureTheory ProbabilityTheory Filter Topology

namespace BauerleRiederMDP.Contracting

open MDPFinance.Contracting

/-- **Lemma 7.1.4** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance*
(2011), Lemma 7.1.4, p.197, PDF p.208). Under the standing assumptions (A) and (C) of Chapter 7
(p.195), for `n, m ∈ ℕ₀` with `n ≥ m`:
a) `J_{nπ} ≤ J_{mπ} + T_∘^m δ` for every policy `π ∈ F^∞`;
b) `J_n ≤ J_m + T_∘^m δ`.

Here `J_{nπ} := T_{f_0} ⋯ T_{f_{n−1}} 0` and `J_n := sup_π J_{nπ}` (p.197),
`δ(x) := sup_π 𝔼^π_x [∑_k β^k r^+(X_k, f_k(X_k))]` (p.195) and
`T_∘ v(x) := sup_{a ∈ D(x)} β ∫ v(x') Q(dx'|x,a)` (p.195).

**Formalization Note.** All objects are the published `MDPFinance.Contracting` bundles:
`Jnpi M M.r π n` is the book's recursion `T_{f_0} ⋯ T_{f_{n−1}} 0` with the `[−∞, ∞)`-valued
integral `∫ v⁺ − ∫ v⁻` (in `EReal`); `Jn` is its supremum over Markov policies `F^∞`; `delta`
is `δ`; `Tcirc` is `T_∘`, whose integral of the possibly non-measurable `[0, ∞)`-valued `δ` is
Mathlib's lower Lebesgue integral (the book integrates `δ` "whenever the integral exists").
(A) is `IntegrabilityAssumptionA` and (C) is `ConvergenceAssumptionC`. -/
theorem lemma_7_1_4 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    (M : MarkovDecisionModel E A) (hA : IntegrabilityAssumptionA M)
    (hC : ConvergenceAssumptionC M) :
    (∀ π : ℕ → E → A, IsPolicyOf M π → ∀ n m : ℕ, m ≤ n → ∀ x : E,
        Jnpi M M.r π n x ≤ Jnpi M M.r π m x + (Tcirc M)^[m] (delta M) x) ∧
      (∀ n m : ℕ, m ≤ n → ∀ x : E,
        Jn M M.r n x ≤ Jn M M.r m x + (Tcirc M)^[m] (delta M) x) := by sorry

end BauerleRiederMDP.Contracting
