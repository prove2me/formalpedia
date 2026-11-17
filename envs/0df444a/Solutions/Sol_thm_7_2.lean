-- Prove2me | solution 1 for thm_7_2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:17:18.563588+00:00
-- url     : https://prove2.me/submissions/acfedf8b-21af-49c2-addf-e4c3b69cdfdd

import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic


-- supplies the canonical Borel `MeasurableSpace` for
-- an abstract `RCLike 𝕜`, as well as measurability of the
--norm and `ENNReal.ofReal`.

/-

 # Theorem 7.2   Measurable functions with zero norm

-/

/-
\begin{thmbox}{7.2 (Measurable Functions with Zero Norm)}
Suppose $X$ is a real-valued or complex-valued measurable
function defined on a measure space $(\Omega,\mathcal{F},\mu)$.
Then, the following are equivalent:
\begin{enumerate}[label=\arabic*.]
    \item $\int_{\Omega} |X|\, d\mu = 0$.
    \item $X$ is equal to $0$ almost everywhere, i.e.,
    there exists a measurable set $A$ with $\mu(A)=0$
    such that $X(\omega)=0$ for all $\omega \in A^c$.
\end{enumerate}
\end{thmbox}

\textit{Proof} Suppose $X=0$ almost everywhere. Let $A$ be
the set mentioned in the theorem. We have
\[
\int |X| = \int_{A^c} |X| + \int_A |X|.
\]

The first term is zero because $X(\omega)=0$ for all
$\omega \in A^c$. To show that the second term is zero,
we consider nonnegative simple function $f$ that is pointwise smaller than the function $|X|1_A$. We can write $f(\omega)$ as $\sum_{i=1}^{n} a_i 1_{E_i}(\omega)$, where $E_i$ is a measurable set inside the set $A$. Since $A$ has measure $0$, all sets $E_i$'s have measure zero, and hence the integral of $f$ is zero. Because it holds for all simple functions $0\le f\le |X|1_A$, the Lebesgue integral of $|X|$ over $A$ is zero.

Conversely, suppose $\int |X|=0$. For each positive integer
$n$, we let $E_n$ denote the event $\{\omega : |X(\omega)|\ge 1/n\}$. The event $E_n$ has measure zero, because
\[
0 = \int |X|\, d\mu \ge \int_{E_n} |X|\, d\mu \ge \int_{E_n} (1/n)\, d\mu \ge (1/n)\mu(E_n),
\]
which is possible only if $\mu(E_n)=0$. We can take the set
$A$ in the theorem to be the union $\cup_n E_n$, which has
measure zero. Then $X(\omega)=0$ for all $\omega \in A^c$.
\hfill $\square$
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory


theorem solution {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜] {μ : Measure Ω}
    {X : Ω → 𝕜} (hX : Measurable X) :
    (∫⁻ ω, ENNReal.ofReal ‖X ω‖ ∂μ = 0) ↔ X =ᵐ[μ] 0 := by
  let nX : Ω → ENNReal := fun ω => ENNReal.ofReal ‖X ω‖
  have hnX : AEMeasurable nX μ := ((hX.norm).ennreal_ofReal).aemeasurable
  constructor
  · intro h_zero
    have hnX_zero : nX =ᵐ[μ] 0 :=
      (MeasureTheory.lintegral_eq_zero_iff' hnX).1 h_zero
    filter_upwards [hnX_zero] with ω hω
    have hnorm : ‖X ω‖ = 0 := by
      simpa [nX] using hω
    exact norm_eq_zero.mp hnorm
  · intro hX_zero
    have hnX_zero : nX =ᵐ[μ] 0 := by
      filter_upwards [hX_zero] with ω hω
      simp [nX, hω]
    exact (MeasureTheory.lintegral_eq_zero_iff' hnX).2 hnX_zero