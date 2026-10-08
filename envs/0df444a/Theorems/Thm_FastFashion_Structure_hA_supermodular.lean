-- Prove2me | Theorems.Thm_FastFashion_Structure_hA_supermodular
-- name    : FastFashion.Structure.hA_supermodular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:09:45.167984+00:00
-- url     : https://prove2.me/theorems/4e04371e-5bad-4650-957c-3ad3bdc401c4
-- title:
--   Appendix §5.1 — $h^{\mathcal A}(q) = \mathbb E[\tau_{\mathcal A}\wedge T]$ is supermodular
-- statement:
--   Let $(N_s)_{s \in \mathcal S}$ be an independent Poisson family with rates $\lambda_s > 0$ on a probability space, and let $T > 0$. For every set of sizes $\mathcal A \subseteq \mathcal S$, the function
--   $$h^{\mathcal A}(q) = \mathbb E[\tau_{\mathcal A} \wedge T], \qquad q \in \mathbb N^{\mathcal S},$$
--   is supermodular on the lattice $\mathbb N^{\mathcal S}$: $h^{\mathcal A}(q) + h^{\mathcal A}(q') \le h^{\mathcal A}(q \vee q') + h^{\mathcal A}(q \wedge q')$ for all $q, q'$.
--
--   Together with identity (2), this gives the supermodularity of the expected sales function in Proposition 1.
--
--   **Formalization Note** Supermodularity is Topkis's notion, the published platform definition `SupermodularOn` with the whole lattice as domain.
-- source:
--   Caro & Gallien, Inventory Management of a Fast-Fashion Retail Network, working paper (August 2, 2007), p. 31, Appendix §5.1, Proof of Proposition 1, last paragraph

import Mathlib
import Definitions.Def_FastFashion_Structure_Model
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn

namespace FastFashion.Structure

open MeasureTheory ProbabilityTheory

theorem hA_supermodular {S Ω : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (lam : S → ℝ) (N : S → ℝ → Ω → ℕ) (T : ℝ)
    (hN : IsPoissonFamily lam N P) (hlam : ∀ s, 0 < lam s) (hT : 0 < T) :
    ∀ A : Finset S, Supermodularity.Monotonicity.SupermodularOn (hA N P T A) Set.univ := by sorry

end FastFashion.Structure
