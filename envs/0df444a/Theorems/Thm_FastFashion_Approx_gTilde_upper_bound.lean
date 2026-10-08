-- Prove2me | Theorems.Thm_FastFashion_Approx_gTilde_upper_bound
-- name    : FastFashion.Approx.gTilde_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:15:05.325964+00:00
-- url     : https://prove2.me/theorems/57146eb7-47ae-4469-90d8-ace03c80b4a1
-- title:
--   §3.1.3, upper-bound claim — the approximation $\tilde g_\lambda(q)$ of (8) is an upper bound for expected sales $g_\lambda(q)$
-- statement:
--   Let $(N_s)_{s\in\mathcal S}$ be an independent Poisson family with rates $\lambda_s > 0$ on a probability space, let $T > 0$, let $\mathcal S^+$ be a nonempty set of major sizes with $\mathcal S^- = \mathcal S \setminus \mathcal S^+$, and for every size $s$ let $\mathcal N(\lambda_s) \subseteq \mathbb N \cup \{\infty\}$ be a nonempty finite set of tangent indices. Then for every inventory vector $q \in \mathbb N^{\mathcal S}$,
--   $$g_\lambda(q) = \mathbb E[G(q)] \;\le\; \tilde g_\lambda(q),$$
--   where $G(q)$ is the sales of (1) and $\tilde g_\lambda$ is the approximation (8) built from the tangents with indices in $\mathcal N(\lambda_s)$.
--
--   This is the guarantee behind the paper's shipment optimization: the deterministic, piecewise-linear objective that replaces the expected sales in the MIP of §3.2 never underestimates them.
--
--   **Formalization Note** $g_\lambda$ is defined from $G$ by (1), not by formula (2). The tangent coefficients are the index-corrected ones of `FastFashion.Approx.Tangents`. The paper's rule (7) for choosing $\mathcal N(\lambda_s)$ ("$b_i \approx 0, 0.3T, \dots$") is approximate; the statement is made for every nonempty finite choice, which includes the paper's. Nonemptiness of $\mathcal S^+$ is an added hypothesis: without a major size the first term of (8), $\lambda_{\mathcal S^+}$ times a minimum over $\emptyset$, has no value.
-- source:
--   Caro & Gallien, Inventory Management of a Fast-Fashion Retail Network, working paper (August 2, 2007), p. 13, §3.1.3, upper-bound claim (sentence after (8))

import Mathlib
import Definitions.Def_FastFashion_Structure_Model
import Definitions.Def_FastFashion_Approx_Tangents

namespace FastFashion.Approx

open MeasureTheory ProbabilityTheory

/-- §3.1.3, upper-bound claim (Caro–Gallien, p. 13): for every choice of nonempty finite tangent
index sets `𝒩(λ_s) ⊆ ℕ ∪ {∞}` and every inventory vector `q ∈ ℕ^S`, the approximation `g̃_λ(q)`
of (8) is an upper bound for the expected sales `g_λ(q) = 𝔼[G(q)]`. -/
theorem gTilde_upper_bound {S Ω : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (lam : S → ℝ) (N : S → ℝ → Ω → ℕ)
    (hN : FastFashion.Structure.IsPoissonFamily lam N P) (hlam : ∀ s, 0 < lam s) (T : ℝ) (hT : 0 < T)
    (Sp : Finset S) (hSp : Sp.Nonempty)
    (Nset : S → Finset (WithTop ℕ)) (hNset : ∀ s, (Nset s).Nonempty) (q : S → ℕ) :
    FastFashion.Structure.expectedSales N P Sp T q ≤ gTilde lam T Sp hSp Nset hNset q := by sorry

end FastFashion.Approx
