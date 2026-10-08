-- Prove2me | Theorems.Thm_FastFashion_Structure_eq_2_optional_sampling
-- name    : FastFashion.Structure.eq_2_optional_sampling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:08:58.141982+00:00
-- url     : https://prove2.me/theorems/cc25065c-04c6-4f20-8a75-ad46bba738d0
-- title:
--   Eq. (2) — $g_\lambda(q) = \lambda_{\mathcal S^+}\mathbb E[\tau_{\mathcal S^+}\wedge T] + \sum_{s\in\mathcal S^-}\lambda_s\mathbb E[\tau_{\mathcal S^+\cup\{s\}}\wedge T]$
-- statement:
--   Let $(N_s)_{s \in \mathcal S}$ be an independent Poisson family with rates $\lambda_s > 0$ on a probability space, let $T > 0$, let $\mathcal S^+$ be the major sizes and $\mathcal S^- = \mathcal S \setminus \mathcal S^+$ the minor sizes. Write $\lambda_{\mathcal S^+} = \sum_{s \in \mathcal S^+} \lambda_s$ and $h^{\mathcal A}(q) = \mathbb E[\tau_{\mathcal A} \wedge T]$. Then for every inventory vector $q \in \mathbb N^{\mathcal S}$, the expected sales $g_\lambda(q) = \mathbb E[G(q)]$ of (1) satisfy
--   $$g_\lambda(q) = \lambda_{\mathcal S^+}\,\mathbb E[\tau_{\mathcal S^+} \wedge T] + \sum_{s \in \mathcal S^-} \lambda_s\, \mathbb E[\tau_{\mathcal S^+ \cup \{s\}} \wedge T]. \qquad (2)$$
--
--   Identity (2) is the step where the Poisson rates enter: it rewrites the expected sales, defined through the counting processes evaluated at random times, as a positive linear combination of the functions $h^{\mathcal A}$ with $\mathcal A = \mathcal S^+$ and $\mathcal A = \mathcal S^+ \cup \{s\}$. Appendix §5.1 restates it as $g = \lambda_{\mathcal S^+} h^{\mathcal S^+} + \sum_{s \in \mathcal S^-} \lambda_s h^{\mathcal S^+ \cup \{s\}}$, and the proof of Proposition 1 rests on it.
--
--   **Formalization Note** $g_\lambda$ is defined as the expectation of $G$ from (1), not by formula (2), so this is a genuine identity. When $\mathcal S^+ = \emptyset$, $\tau_\emptyset = +\infty$ and the first term vanishes.
-- source:
--   Caro & Gallien, Inventory Management of a Fast-Fashion Retail Network, working paper (August 2, 2007), pp. 11–12, §3.1.3, Eq. (2); restated p. 31, Appendix §5.1

import Mathlib
import Definitions.Def_FastFashion_Structure_Model

namespace FastFashion.Structure

open MeasureTheory ProbabilityTheory

theorem eq_2_optional_sampling {S Ω : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (lam : S → ℝ) (N : S → ℝ → Ω → ℕ) (T : ℝ)
    (hN : IsPoissonFamily lam N P) (hlam : ∀ s, 0 < lam s) (hT : 0 < T)
    (Sp : Finset S) :
    ∀ q : S → ℕ, expectedSales N P Sp T q =
      (∑ s ∈ Sp, lam s) * hA N P T Sp q + ∑ s ∈ Spᶜ, lam s * hA N P T (insert s Sp) q := by sorry

end FastFashion.Structure
