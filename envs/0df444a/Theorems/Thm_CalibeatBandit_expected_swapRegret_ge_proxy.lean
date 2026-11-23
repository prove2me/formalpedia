-- Prove2me | Theorems.Thm_CalibeatBandit_expected_swapRegret_ge_proxy
-- name    : CalibeatBandit.expected_swapRegret_ge_proxy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-23T18:37:52.821552+00:00
-- url     : https://prove2.me/theorems/12ebde0a-217d-4d06-bb8e-ae8a6f45c1f3
-- title:
--   Proof of Theorem 4.1 — from the expected proxy gain to swap regret: $\mathbb E[\mathrm{SR}_T]\ge a\,\mathbb E[G]-Kc\sqrt{2T\log(2K)}$
-- statement:
--   **Setting.** Let $(\Omega,P)$ be a probability space with a filtration $(\mathcal F_t)$, $K$ actions and horizon $T$. For $t<T$ let $y_t\in[0,1]^K$ be rewards, $I_t$ the action played, $q_t$ a probability vector and $u_t\in[0,1]^K$, all measurable in $\omega$. Fix constants $a$ and $c>0$ and put
--
--   $$d_{i,t,j}=\mathbf 1[I_t=i]\big(y_t(j)-y_t(i)\big)-a\,q_t(i)\big(u_t(j)-u_t(i)\big).$$
--
--   **Statement.** If for all $i,j$ and $t<T$ the variable $d_{i,t,j}$ is $\mathcal F_{t+1}$-measurable, bounded by $c$ in absolute value and satisfies $\mathbb E[d_{i,t,j}\mid\mathcal F_t]=0$, then
--
--   $$\mathbb E\big[\mathrm{SR}_T(y,I)\big]\ \ge\ a\,\mathbb E\big[\mathrm{SR}^{p}_T(q,u)\big]-K\,c\sqrt{2T\log(2K)},$$
--
--   where $\mathrm{SR}_T(y,I)=\max_\sigma\sum_{t<T}\big(y_t(\sigma(I_t))-y_t(I_t)\big)$ is the swap regret of the play and $\mathrm{SR}^p_T(q,u)=\max_\sigma\sum_{t<T}\sum_iq_t(i)\big(u_t(\sigma(i))-u_t(i)\big)$ is the pseudo swap regret of $q$ against $u$.
--
--   **Role.** The hypothesis says that, given the past, the realized gain of swapping $i$ to $j$ has conditional mean $a$ times the proxy gain $q_t(i)(u_t(j)-u_t(i))$. The conclusion transfers a lower bound on the expected proxy (the quantity $G$ of §4) to the actual swap regret, at the price of one maximal inequality (Lemma 4.10) per action. It is the last step of the proof of Theorem 4.1, where $a=\eta/48$ and $u_t$ are the bonus probabilities, and it does not depend on the tree construction.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (STOC 2027 submission 1457), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1457.pdf, proof of Theorem 4.1, pp. 20–21 (the martingale argument). Statement taken from jasonhartline's accepted Lean proof of CalibeatBandit.theorem_4_1 (submission 0ae8d87e-4337-4d82-8722-8eeded8a7691).

import Definitions.Def_CalibeatBandit_hard_tree_analysis

set_option autoImplicit false

open CalibeatBandit Filter MeasureTheory Set InformationTheory ProbabilityTheory
open scoped Interval ENNReal BigOperators

theorem CalibeatBandit.expected_swapRegret_ge_proxy {K T : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (info : Filtration ℕ mΩ)
    (anchor : Fin K) (a c : ℝ) (hc : 0 < c)
    (q u y : Ω → ℕ → Fin K → ℝ) (I : Ω → ℕ → Fin K)
    (hy : ∀ t < T, ∀ ω j, y ω t j ∈ Set.Icc (0 : ℝ) 1)
    (hym : ∀ t < T, ∀ j, Measurable (fun ω => y ω t j))
    (hI : ∀ t < T, Measurable (fun ω => I ω t))
    (hq : ∀ t < T, ∀ ω, IsProbVec (q ω t))
    (hu : ∀ t < T, ∀ ω j, u ω t j ∈ Set.Icc (0 : ℝ) 1)
    (hqm : ∀ t < T, ∀ j, Measurable (fun ω => q ω t j))
    (hum : ∀ t < T, ∀ j, Measurable (fun ω => u ω t j)) :
    let d (i : Fin K) (t : ℕ) (j : Fin K) (ω : Ω) :=
      (Pi.single (I ω t) (1 : ℝ) : Fin K → ℝ) i * (y ω t j - y ω t i) -
        a * (q ω t i * (u ω t j - u ω t i))
    (∀ t < T, ∀ i j, Measurable[info (t + 1)] (d i t j)) →
    (∀ t < T, ∀ i j ω, |d i t j ω| ≤ c) →
    (∀ t < T, ∀ i j, condExp (info t) P (d i t j) =ᵐ[P] 0) →
    a * (∫ ω, pseudoSwapRegret T (q ω) (u ω) ∂P) -
      K * (c * Real.sqrt (2 * T * Real.log (2 * K))) ≤
      ∫ ω, swapRegret T (y ω) (I ω) ∂P := by sorry
