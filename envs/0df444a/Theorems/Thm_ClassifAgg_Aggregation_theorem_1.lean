-- Prove2me | Theorems.Thm_ClassifAgg_Aggregation_theorem_1
-- name    : ClassifAgg.Aggregation.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:17:30.471747+00:00
-- url     : https://prove2.me/theorems/caa402ae-0e62-4968-9244-08c1f51c16f8
-- title:
--   Theorem 1, p. 140 — ERM over an ε-net attains sup_{π∈𝒫} E d(Ĝ_n, G*) = O(n^{−κ/(2κ+ρ−1)})
-- statement:
--   Let $\kappa\ge1$, $0<\rho<1$, $a>0$ and $\varepsilon=an^{-1/(1+\rho)}$. Let $\mathcal P$ be a $(\mathcal G^*,\kappa,\rho)$-class of joint distributions of $(X,Y)$ (Definition 4, with constants $A$, $c_0$, $\varepsilon_0$), and, for each $n\ge1$, let $\mathcal N=\mathcal N_n$ be an $\varepsilon$-net of Borel sets on $\mathcal G^*$ for the pseudodistance $d_\triangle$ or $d_{\triangle,e}$, such that $\mathcal N$ has complexity bound $\rho$. Then the empirical risk minimizer
--   $$\hat G_n=\arg\min_{G\in\mathcal N}R_n(G)\tag{8}$$
--   satisfies
--   $$\sup_{\pi\in\mathcal P}E_{\pi,n}\big(d(\hat G_n,G^*)\big)=O\big(n^{-\kappa/(2\kappa+\rho-1)}\big),\qquad n\to\infty.$$
--
--   This is the rate for a known class $\mathcal G^*$; it approaches $n^{-1}$ as $\kappa\to1$, $\rho\to0$. In the proof of Theorem 3 it bounds the risk of $G_{nj^*}$.
--
--   **Formalization Note** The supremum over $\mathcal P$ is written as a bound holding for every $\pi\in\mathcal P$ with one constant $C$ and one threshold $N_0$. "arg min" is any minimizer at every sample. The net for $d_\triangle$ is required for the design law of every $\pi\in\mathcal P$, and its complexity bound uses the class's constant $A$ (no loss, since a complexity bound with $A$ holds with any larger constant). The expectation is a Lebesgue integral over the sample, so it carries the hypothesis that $\{(s,x):x\in\hat G_n(s)\}$ is measurable; without it the integral of a non-measurable integrand would be $0$. The integrand is then bounded and measurable, so no integrability hypothesis is needed.
-- source:
--   Tsybakov (2004), Ann. Statist. 32, Theorem 1, p. 140; proof pp. 148–151

import Mathlib
import Definitions.Def_ClassifAgg_Aggregation_Setup

namespace ClassifAgg.Aggregation

open MeasureTheory

theorem theorem_1 {d : ℕ} (P : Set (Measure (E d) × (E d → ℝ)))
    (cls : Set (Set (E d))) (κ ρ A c0 ε0 a : ℝ)
    (hP : IsGKRClass P cls κ ρ A c0 ε0) (ha : 0 < a)
    (net : ℕ → Set (Set (E d)))
    (hnetMeas : ∀ n : ℕ, 1 ≤ n → ∀ G ∈ net n, MeasurableSet G)
    (hnet : ∀ n : ℕ, 1 ≤ n →
      (∀ π ∈ P, IsNet π.1 (a * (n : ℝ) ^ (-1 / (1 + ρ))) (net n) cls) ∨
        IsEmpNet n (a * (n : ℝ) ^ (-1 / (1 + ρ))) (net n) cls)
    (hcompl : ∀ n : ℕ, 1 ≤ n → ∀ π ∈ P, HasComplexityBound π.1 (net n) ρ A)
    (Ghat : (n : ℕ) → (Fin n → E d × Bool) → Set (E d))
    (hERM : ∀ n : ℕ, 1 ≤ n → IsERM (net n) (Ghat n))
    (hmeas : ∀ n, MeasurableSet {p : (Fin n → E d × Bool) × E d | p.2 ∈ Ghat n p.1}) :
    ∃ C : ℝ, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n → ∀ π ∈ P,
      ∫ s, excess π.1 π.2 (Ghat n s) ∂(sampleLaw π.1 π.2 n)
        ≤ C * (n : ℝ) ^ (-κ / (2 * κ + ρ - 1)) := by sorry

end ClassifAgg.Aggregation
