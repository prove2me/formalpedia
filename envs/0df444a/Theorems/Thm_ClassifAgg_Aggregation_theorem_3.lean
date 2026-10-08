-- Prove2me | Theorems.Thm_ClassifAgg_Aggregation_theorem_3
-- name    : ClassifAgg.Aggregation.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:17:52.107848+00:00
-- url     : https://prove2.me/theorems/1c5e928b-91cc-4e39-8489-a7d522d372d2
-- title:
--   Theorem 3, p. 144 — the adaptive classifier satisfies sup_{π∈𝒫_j} E d(G*_n, G*) ≤ C (log⁴ n / n)^{κ/(2κ+ρ_j−1)} for every j
-- statement:
--   Let assumptions (A3) and (A4) hold and let, for some $\kappa\ge1$, $\mathcal P_j$ be $(\mathcal G_j,\kappa,\rho_j)$-classes of joint distributions of $(X,Y)$, $j=1,\dots,N$. Suppose $N=N_n=O(n^\beta)$ as $n\to\infty$ for some finite $\beta>0$, and that $\rho_1=\rho_{\min}$ and $\rho_N=\rho_{\max}$ do not depend on $n$. Then the adaptive classifier $G^*_n=G_{n\hat j}$ satisfies
--   $$\sup_{\pi\in\mathcal P_j}E_{\pi,n}\big(d(G^*_n,G^*)\big)\le C\left(\frac{\log^4 n}{n}\right)^{\kappa/(2\kappa+\rho_j-1)}$$
--   for any $j=1,\dots,N$, where $n>1$ and $C$ is a finite constant that does not depend on $n$.
--
--   Up to a logarithmic factor, the adaptive classifier attains the optimal rate $n^{-\kappa/(2\kappa+\rho_j-1)}$ simultaneously on all the classes, without knowing which class contains the Bayes set $G^*$ or the margin parameter $\kappa$.
--
--   **Formalization Note** The data of Section 3 ($N_n$, classes, approximating sets, complexities, net constants $a_j$, distribution classes) are indexed by $n$, and the hypotheses are those of the definition `Setup`: one $A$, $c_0$, $\varepsilon_0$ for all classes, condition (7) uniformly over the whole family unless $\varepsilon_0=1$, and complexity bounds of the approximating sets for the design law of every distribution in the family. $C$ is chosen after the setup and before $n$, $j$ and $\pi$; it is uniform in $j$, as the proof of Corollary 1 uses with an $n$-dependent $j$. "$n>1$" is $n\ge2$, where $\log n>0$; $\log^4n=(\log n)^4$. The empirical risk minimizers are any minimizers. The expectation carries the hypothesis that $\{(s,x):x\in G^*_n(s)\}$ is measurable; without it the integral of a non-measurable integrand would be $0$ and the bound would be free.
-- source:
--   Tsybakov (2004), Ann. Statist. 32, Theorem 3, p. 144; procedure pp. 143–144; proof pp. 152–154

import Mathlib
import Definitions.Def_ClassifAgg_Aggregation_Setup

namespace ClassifAgg.Aggregation

open MeasureTheory

theorem theorem_3 {d : ℕ} (S : AggSetup d) (κ ρmin ρmax β a A c0 ε0 : ℝ)
    (hS : AggAssumptions S κ ρmin ρmax β a A c0 ε0)
    (Ghat : (n : ℕ) → ℕ → (Fin n → E d × Bool) → Set (E d))
    (hERM : ∀ n k, 1 ≤ k → k ≤ S.N n → IsERM (S.net n k) (Ghat n k))
    (hmeas : ∀ n, MeasurableSet {p : (Fin n → E d × Bool) × E d |
      p.2 ∈ adaptive n (S.N n) (S.net n) (S.ρ n) (Ghat n) p.1}) :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ j : ℕ, 1 ≤ j → j ≤ S.N n → ∀ π ∈ S.P n j,
      ∫ s, excess π.1 π.2 (adaptive n (S.N n) (S.net n) (S.ρ n) (Ghat n) s)
          ∂(sampleLaw π.1 π.2 n)
        ≤ C * ((Real.log n) ^ 4 / n) ^ (κ / (2 * κ + S.ρ n j - 1)) := by sorry

end ClassifAgg.Aggregation
