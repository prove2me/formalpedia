-- Prove2me | Theorems.Thm_FastFashion_Structure_stopMin_supermodular_pathwise
-- name    : FastFashion.Structure.stopMin_supermodular_pathwise
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:08:58.161489+00:00
-- url     : https://prove2.me/theorems/3c7759ae-2484-4a5e-b9f2-7dfe0784ec87
-- title:
--   Appendix §5.1 — on every sample path $q \mapsto \tau_{\mathcal A}\wedge T$ is supermodular
-- statement:
--   Let $(N_s)_{s \in \mathcal S}$ be an independent Poisson family and $T$ a time horizon. For every set of sizes $\mathcal A \subseteq \mathcal S$ and every outcome $\omega$, the function
--   $$q \longmapsto \tau_{\mathcal A}(q)(\omega) \wedge T = \min_{s \in \mathcal A} \tau_s(q_s)(\omega) \wedge T$$
--   is supermodular on the lattice $\mathbb N^{\mathcal S}$ (componentwise order): for all $q, q'$,
--   $$f(q) + f(q') \le f(q \vee q') + f(q \wedge q').$$
--
--   This is the sample-path step of the supermodularity part of Proposition 1: $\tau_{\mathcal A} \wedge T$ is a minimum of functions each non-decreasing in a single variable.
--
--   **Formalization Note** Supermodularity is Topkis's notion, the published platform definition `SupermodularOn` with the whole lattice as domain. Only the path properties of the Poisson family are used, and no assumption on $T$ is needed.
-- source:
--   Caro & Gallien, Inventory Management of a Fast-Fashion Retail Network, working paper (August 2, 2007), p. 31, Appendix §5.1, Proof of Proposition 1, last paragraph, first clause

import Mathlib
import Definitions.Def_FastFashion_Structure_Model
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn

namespace FastFashion.Structure

open MeasureTheory ProbabilityTheory

theorem stopMin_supermodular_pathwise {S Ω : Type*} [Fintype S] [DecidableEq S]
    [MeasurableSpace Ω] (P : Measure Ω) (lam : S → ℝ) (N : S → ℝ → Ω → ℕ) (T : ℝ)
    (hN : IsPoissonFamily lam N P) :
    ∀ (A : Finset S) (ω : Ω),
      Supermodularity.Monotonicity.SupermodularOn (fun q : S → ℕ => stopMin N A q T ω)
        Set.univ := by sorry

end FastFashion.Structure
