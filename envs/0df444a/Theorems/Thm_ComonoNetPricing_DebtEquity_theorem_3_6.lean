-- Prove2me | Theorems.Thm_ComonoNetPricing_DebtEquity_theorem_3_6
-- name    : ComonoNetPricing.DebtEquity.theorem_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:39.854141+00:00
-- url     : https://prove2.me/theorems/0c503bb2-bd53-43e5-8237-1de97bfdbe59
-- title:
--   Theorem 3.6, p. 13, corrected (f right-continuous) — default probabilities and expected wealth, payments and equity under comonotonic endowments
-- statement:
--   For a positive integer $n$, consider the Rogers–Veraart network under the standing assumptions ($\pi_{ij}\ge0$, $\pi_{ii}=0$, $\sum_j\pi_{ij}<1$, $\bar p_i>0$, $\alpha_x,\alpha_L\in[0,1]$), with greatest clearing wealth $V$, payments $p = \bar p - V^-$ and equity $E = V^+$. Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and let the endowments be comonotonic, $X = f(q)$ (Assumption 3.2), where
--
--   1. $q$ is a random variable with $q \ge 0$ almost surely;
--   2. $f : \mathbb R_+ \to \mathbb R^n_+$ is nondecreasing and right-continuous;
--   3. each component of $X = f(q)$ is integrable.
--
--   Let $q^*_i = \inf\{q\ge0 \mid V_i(f(q))\ge0\} \in [0,\infty]$ (Definition 3.4), and assume the banks are ordered so that $q^*_1 \ge q^*_2 \ge \dots \ge q^*_n$, with $q^*_0 = \infty$ and $q^*_{n+1} = 0$ (Assumption 3.5). Let $\Delta_k, \delta_k$ be as in the definition (with $\Delta_0 = I$, $\delta_0 = (I-\Pi^\top)\bar p$) and write
--   $$T_k = \Delta_k\,\mathbb E\big[f(q)\,\mathbb I_{\{q\in[q^*_{k+1},q^*_k)\}}\big] - \delta_k\,\mathbb P\big(q\in[q^*_{k+1},q^*_k)\big).$$
--   Then for every bank $i$,
--   $$\mathbb P(V_i(X)<0) = \mathbb P(q<q^*_i),\qquad \mathbb E[V_i(X)] = e_i^\top\sum_{k=0}^n T_k,$$
--   $$\mathbb E[p_i(X)] = \bar p_i + e_i^\top\sum_{k=i}^n T_k,\qquad \mathbb E[E_i(X)] = e_i^\top\sum_{k=0}^{i-1} T_k.$$
--
--   These are the paper's closed-form prices of debt and equity: under comonotonic endowments the factor space splits into $n+1$ intervals with constant default sets, instead of the $2^n$ default regions of a general endowment.
--
--   **Formalization Note** Right-continuity of $f$ on $[0,\infty)$ is **added** to the printed hypotheses. As printed the theorem is false: with $n=1$, $\Pi=0$, $\bar p=1$, $f=0$ on $[0,1]$ and $f=2$ on $(1,\infty)$, and $q\in\{1,2\}$ with probability $\tfrac12$ each, $\mathbb P(V_1<0)=\tfrac12$ while $\mathbb P(q<q^*_1)=\mathbb P(q<1)=0$. The paper's description of $q^*_i$ as "the minimal value such that firm $i$ is solvent" presupposes the infimum is attained, which right-continuity of $f$ provides. In Lean, bank `i : Fin n` is the paper's bank $i+1$, so the payment sum runs over $k \in \{i+1,\dots,n\}$ (`Finset.Ioc i n`) and the equity sum over $k\in\{0,\dots,i\}$ (`Finset.range (i+1)`). $X = f(q)$ is taken literally (not only in distribution). The thresholds are in $[0,\infty]$ and compared with the factor through `ENNReal.ofReal`. Expectations are Bochner integrals and probabilities are measures of events; integrability of the endowments is a hypothesis, as $X \in (L^1_+)^n$ on the page.
-- source:
--   Banerjee & Feinstein, Pricing of debt and equity in a financial network with comonotonic endowments, arXiv:1810.01372v5, p. 13, Theorem 3.6 (with Assumption 3.2 p. 10, Definition 3.4 and Assumption 3.5 p. 12)

import Mathlib
import Definitions.Def_ComonoNetPricing_DebtEquity_Network
import Definitions.Def_ComonoNetPricing_DebtEquity_Model

namespace ComonoNetPricing.DebtEquity

open Matrix

open MeasureTheory

/-- Theorem 3.6, p. 13, corrected: `f` is additionally assumed right-continuous on `[0, ∞)`
(as printed, without it, the theorem fails; see the mission description). Endowments
`X = f(q)` with `q ≥ 0` a.s. measurable, `f : ℝ₊ → ℝⁿ₊` nondecreasing, `X` integrable
(Assumption 3.2), banks ordered by `q*_1 ≥ ⋯ ≥ q*_n` (Assumption 3.5). With
`term k = Δ_k E[f(q) 1{q ∈ [q*_{k+1}, q*_k)}] − δ_k P(q ∈ [q*_{k+1}, q*_k))`, for every bank
`i : Fin n` (the paper's bank `i + 1`):
`P(V_i(X) < 0) = P(q < q*_i)`, `E[V_i(X)] = ∑_{k=0}^n (term k)_i`,
`E[p_i(X)] = p̄_i + ∑_{k=i+1}^n (term k)_i` and `E[E_i(X)] = ∑_{k=0}^{i} (term k)_i`
(the paper's sums over `k = i, …, n` and `k = 0, …, i − 1` for its bank `i`). -/
theorem theorem_3_6 {n : ℕ} (hn : 0 < n) (N : Network n) (hN : N.Standing)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q : Ω → ℝ) (hq : Measurable q) (hq0 : ∀ᵐ ω ∂P, 0 ≤ q ω)
    (f : ℝ → Fin n → ℝ) (hf_mono : MonotoneOn f (Set.Ici 0)) (hf_nonneg : ∀ s, 0 ≤ s → 0 ≤ f s)
    (hf_rc : ∀ s, 0 ≤ s → ContinuousWithinAt f (Set.Ici s) s)
    (hX : ∀ j, Integrable (fun ω => f (q ω) j) P)
    (hord : Antitone (N.qstar f)) (i : Fin n) :
    let term : ℕ → Fin n → ℝ := fun k =>
      N.DeltaK k *ᵥ (fun j => ∫ ω, (N.Ik f q k).indicator (fun ω => f (q ω) j) ω ∂P)
        - (P (N.Ik f q k)).toReal • N.deltaK k
    P {ω | N.clearingWealth (f (q ω)) i < 0} = P {ω | ENNReal.ofReal (q ω) < N.qstar f i} ∧
      ∫ ω, N.clearingWealth (f (q ω)) i ∂P = ∑ k ∈ Finset.range (n + 1), term k i ∧
      ∫ ω, N.payment (f (q ω)) i ∂P = N.pbar i + ∑ k ∈ Finset.Ioc i.val n, term k i ∧
      ∫ ω, N.equity (f (q ω)) i ∂P = ∑ k ∈ Finset.range (i.val + 1), term k i := by sorry

end ComonoNetPricing.DebtEquity
