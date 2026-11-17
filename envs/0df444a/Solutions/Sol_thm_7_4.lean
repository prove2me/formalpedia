-- Prove2me | solution 1 for thm_7_4
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:18:15.948792+00:00
-- url     : https://prove2.me/submissions/741361ad-8da5-43e4-89cf-7493684cd4e1

import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic


/-

  # Theorem 7.4 Dominated convergence theorem

-/

/-
\begin{thmbox}{7.4 (Dominated Convergence Theorem)}
For $n=1,2,3,\dots$, let $X_n(\omega)$ be
$\bar{\mathbb{R}}$-valued measurable functions defined
on a measure space $(\Omega,\mathcal{F},\mu)$, converging
almost everywhere to $X(\omega)$,
\[
X_n \to X \quad \text{a.e.}
\]

If there exists a nonnegative integrable function $Y$
such that $|X_n|\le Y$ a.e. for all $n$, then

(1) $X$ is Lebesgue integrable, i.e., $X\in L^1(\mu)$, and

(2)
\[
\lim_{n\to\infty} \int X_n\, d\mu = \int X\, d\mu = \int \lim_{n\to\infty} X_n\, d\mu.
\]
\end{thmbox}

\textit{Proof} By the assumption that $|X_n|\le Y$ a.e.,
we can find for each $n$ a measurable set $E_n$ such that
$\mu(E_n^c)=0$ and $|X_n(\omega)|\le Y(\omega)$ for all $\omega \in E_n$. Also, we can find a measurable set $E_0$ such that $\mu(E_0^c)=0$ and $X_n(\omega)\to X(\omega)$ for all $\omega \in E_0$. For $\omega$ in the set $E\triangleq \cap_{n\ge 0} E_n$, we have $|X_n(\omega)|\le Y(\omega)$ and $X_n(\omega)\to X(\omega)$.

We next observe that $X_n$ is integrable for all $n$,
since $\int |X_n| \le \int Y < \infty$.

Although we do not know the value of $X(\omega)$ for
$\omega \in E_0^c$, we may set $X(\omega)$ to $0$ for
$\omega \in E_0^c$ without loss of generality. Since
$X_n(\omega)$ converges to $X(\omega)$ for all $\omega \in E_0$ by assumption, the function $X$ is a measurable function. (See the remark at the end of Section 7.1)

Consider the difference $|X_n-X|$. By applying the triangle
inequality for real numbers, we have
\[
|X_n(\omega)-X(\omega)| \le |X_n(\omega)|+|X(\omega)| \le 2Y(\omega)
\]
for each $\omega \in E$. Hence $2Y-|X_n-X|\ge 0$ almost everywhere. By Fatou's lemma,
\begin{equation}
\int \liminf_n (2Y-|X_n-X|) \le \liminf_n \int (2Y-|X_n-X|).
\tag{7.2}
\end{equation}

Since $|X_n-X|\to 0$ as $n\to\infty$, the left-hand side equals $\int 2Y$, and the right-hand side becomes
\[
\liminf_n \left( \int 2Y + \int -|X_n-X| \right)
=
\int 2Y - \limsup_n \int |X_n-X|.
\]

In the last step, we have pulled out the constant $\int 2Y$, which does not depend on $n$, and change liminf to limsup. Because $\int 2Y$ is finite, we can subtract it from both sides of (7.2) to obtain
\[
0 \ge \limsup_n \int |X_n-X|.
\]

The limsup of a sequence of nonnegative real numbers $\int |X_n-X|$ should be nonnegative. Hence, $\limsup_n \int |X_n-X|=0$, and this is possible only when $\int |X_n-X|$ is actually converging to $0$,
\begin{equation}
\lim_{n\to\infty} \int |X_n-X| = 0.
\tag{7.3}
\end{equation}

By the triangle inequality for real numbers and monotonic property for integrals,
\[
\int |X| = \int |X-X_n+X_n| \le \int |X-X_n| + \int |X_n|,
\]
which holds for any positive integer $n$. By (7.3), for any arbitrarily small $\epsilon>0$, we can choose a sufficiently large $n$ such that $\int |X-X_n|<\epsilon$. We then use the assumption that $|X_n|\le Y$ to see that $\int |X| \le \epsilon + \int |Y| < \infty$. Therefore, by Theorem 6.6, $X$ is integrable. This proves (1).

We apply the triangle inequality (Theorem 7.1) to get
\[
\left|\int X_n - X\, d\mu\right| \le \int |X_n-X|\, d\mu.
\]

Because $\int |X_n-X|\, d\mu \to 0$ as $n\to\infty$, we have $|\int X_n - X\, d\mu|\to 0$ as $n\to\infty$. This is the same as saying that $\int X_n\, d\mu \to \int X\, d\mu$ as $n\to\infty$. This proves the equalities in (2) and completes the proof of the dominated convergence theorem. \hfill $\square$
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory


theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X Y : Ω → ℝ)
    (hXm : ∀ n, AEStronglyMeasurable (Xn n) μ)
    (hYint : Integrable Y μ)
    (h_bound : ∀ n, ∀ᵐ ω ∂μ, ‖Xn n ω‖ ≤ Y ω)
    (h_lim : ∀ᵐ ω ∂μ, Tendsto (fun n => Xn n ω) atTop (nhds (X ω))) :
  Integrable X μ ∧
    Tendsto (fun n => ∫ ω, Xn n ω ∂μ) atTop (nhds (∫ ω, X ω ∂μ)) := by
  have hX_meas : AEStronglyMeasurable X μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hXm h_lim
  have h_bound_all : ∀ᵐ ω ∂μ, ∀ n, ‖Xn n ω‖ ≤ Y ω :=
    eventually_countable_forall.2 h_bound
  have hX_bound : ∀ᵐ ω ∂μ, ‖X ω‖ ≤ Y ω := by
    filter_upwards [h_bound_all, h_lim] with ω hω_bound hω_lim
    have hnorm_tendsto : Tendsto (fun n => ‖Xn n ω‖) atTop (nhds ‖X ω‖) :=
      (continuous_norm.tendsto (X ω)).comp hω_lim
    have hmem : ∀ᶠ n in atTop, ‖Xn n ω‖ ∈ Set.Iic (Y ω) :=
      Filter.Eventually.of_forall fun n => hω_bound n
    have hlimit_mem : ‖X ω‖ ∈ Set.Iic (Y ω) :=
      IsClosed.mem_of_tendsto isClosed_Iic hnorm_tendsto hmem
    simpa [Set.mem_Iic] using hlimit_mem
  have hX_int : Integrable X μ :=
    Integrable.mono' hYint hX_meas hX_bound
  have h_tendsto :
      Tendsto (fun n => ∫ ω, Xn n ω ∂μ) atTop (nhds (∫ ω, X ω ∂μ)) :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      Y hXm hYint h_bound h_lim
  exact ⟨hX_int, h_tendsto⟩