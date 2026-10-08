-- Prove2me | Theorems.Thm_FastFashion_Structure_delta_hA_integral_formula
-- name    : FastFashion.Structure.delta_hA_integral_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:09:11.619072+00:00
-- url     : https://prove2.me/theorems/7131a9ce-38c1-4666-8743-8168ff781cf8
-- title:
--   Appendix §5.1 display — $\Delta_s h^{\mathcal A}(q)$ as an integral, last line corrected to $\frac1{\lambda_s}\mathbb P(\tau_s(q_s+1)\le\tau_{\mathcal A\setminus\{s\}}\wedge T)$
-- statement:
--   Let $(N_s)_{s \in \mathcal S}$ be an independent Poisson family with rates $\lambda_s > 0$ on a probability space, let $T > 0$, let $\mathcal A \subseteq \mathcal S$ be a set of sizes, $s \in \mathcal A$, and $q \in \mathbb N^{\mathcal S}$. With $h^{\mathcal A}(q) = \mathbb E[\tau_{\mathcal A} \wedge T]$ and $\Delta_s h^{\mathcal A}(q) = h^{\mathcal A}(q + e_s) - h^{\mathcal A}(q)$,
--   $$\begin{aligned}
--   \Delta_s h^{\mathcal A}(q) &= \int_0^T \big[\mathbb P(\tau_s(q_s+1) > t) - \mathbb P(\tau_s(q_s) > t)\big] \prod_{s' \in \mathcal A \setminus \{s\}} \mathbb P(\tau_{s'}(q_{s'}) > t)\,dt \\
--   &= \int_0^T \mathbb P(N_s(t) = q_s) \prod_{s' \in \mathcal A \setminus \{s\}} \mathbb P(\tau_{s'}(q_{s'}) > t)\,dt \\
--   &= \frac{1}{\lambda_s}\,\mathbb P\big(\tau_s(q_s+1) \le \tau_{\mathcal A \setminus \{s\}} \wedge T\big).
--   \end{aligned}$$
--
--   The display expresses the marginal value of one more unit of size $s$ as the (scaled) probability that this unit is demanded before the display is removed and before the end of the period; its monotonicity in $q$ gives the discrete concavity and the cross-monotonicity of $h^{\mathcal A}$.
--
--   **Formalization Note** The paper prints the last line as $\mathbb P(\tau_s(q_s) \le \tau_{\mathcal A\setminus\{s\}} \wedge T)$, which is false: the integral has the dimension of a time, and for $\mathcal A = \{s\}$, $q_s = 0$, $\lambda_s = T = 1$ the printed value is $1$ while $\Delta_s h^{\mathcal A}(q) = 1 - e^{-1}$. Since $\tau_s(q_s+1)$ has density $\lambda_s \mathbb P(N_s(t) = q_s)$, the correct value is the one stated here; the first two lines are as printed. The hypothesis $s \in \mathcal A$ is implicit in the display (the factor for $s$ is taken out of the product; for $s \notin \mathcal A$ one has $\Delta_s h^{\mathcal A} = 0$). $\mathbb P(\tau > t)$ is written with $\tau \in \mathbb R \cup \{+\infty\}$ and $\tau_{\emptyset} = +\infty$; the integrals are interval integrals over $(0, T]$ of bounded measurable functions of $t$, and $\mathbb P(E)$ is the real number `(P E).toReal`.
-- source:
--   Caro & Gallien, Inventory Management of a Fast-Fashion Retail Network, working paper (August 2, 2007), p. 31, Appendix §5.1, Proof of Proposition 1, displayed equation for Δ_s h^A(q) (last line corrected)

import Mathlib
import Definitions.Def_FastFashion_Structure_Model

namespace FastFashion.Structure

open MeasureTheory ProbabilityTheory

theorem delta_hA_integral_formula {S Ω : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (lam : S → ℝ) (N : S → ℝ → Ω → ℕ) (T : ℝ)
    (hN : IsPoissonFamily lam N P) (hlam : ∀ s, 0 < lam s) (hT : 0 < T)
    (A : Finset S) (q : S → ℕ) (s : S) (hs : s ∈ A) :
    delta (hA N P T A) s q =
        ∫ t in (0)..T,
          ((P {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s (q + Pi.single s 1) ω}).toReal
            - (P {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s q ω}).toReal)
          * ∏ s' ∈ A.erase s, (P {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s' q ω}).toReal ∧
    (∫ t in (0)..T,
          ((P {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s (q + Pi.single s 1) ω}).toReal
            - (P {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s q ω}).toReal)
          * ∏ s' ∈ A.erase s, (P {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s' q ω}).toReal) =
        ∫ t in (0)..T,
          (P {ω | N s t ω = q s}).toReal
          * ∏ s' ∈ A.erase s, (P {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s' q ω}).toReal ∧
    (∫ t in (0)..T,
          (P {ω | N s t ω = q s}).toReal
          * ∏ s' ∈ A.erase s, (P {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s' q ω}).toReal) =
        (1 / lam s) *
          (P {ω | stockoutTime N s (q + Pi.single s 1) ω
                    ≤ min (tauMin N (A.erase s) q ω) ((T : ℝ) : WithTop ℝ)}).toReal := by sorry

end FastFashion.Structure
