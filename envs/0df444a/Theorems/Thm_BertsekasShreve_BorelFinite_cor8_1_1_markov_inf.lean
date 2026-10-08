-- Prove2me | Theorems.Thm_BertsekasShreve_BorelFinite_cor8_1_1_markov_inf
-- name    : BertsekasShreve.BorelFinite.cor8_1_1_markov_inf
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:56:28.442102+00:00
-- url     : https://prove2.me/theorems/27e2225e-e16f-4245-ae3b-99a746cbc9c5
-- title:
--   Corollary 8.1.1 — the K-stage optimal cost is the infimum over Markov policies
-- statement:
--   Consider the finite horizon Borel model of Definition 8.1 and assume (F⁺) or (F⁻). For $K=1,2,\dots,N$,
--   $$J^*_K(x)=\inf_{\pi\in\Pi}J_{K,\pi}(x)\qquad\forall x\in S,$$
--   where $\Pi$ is the set of all Markov policies.
--
--   Admitting history-dependent randomized policies therefore does not lower the optimal cost; it only matters for the existence of $\varepsilon$-optimal nonrandomized policies.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 194, Corollary 8.1.1

import Mathlib
import Definitions.Def_BertsekasShreve_BorelFinite_Model
import Definitions.Def_BertsekasShreve_BorelFinite_Policy

namespace BertsekasShreve.BorelFinite

/-- **Corollary 8.1.1** (p. 194). Under (F⁺) or (F⁻), for `K = 1, …, N`,
`J*_K(x) = inf_{π ∈ Π} J_{K,π}(x)` for every `x ∈ S`, `Π` being the set of Markov policies. -/
theorem cor8_1_1_markov_inf {S C W : Type*}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [Nonempty S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [Nonempty C]
    [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [Nonempty W]
    (M : Model S C W)
    (hF : FPlus M ∨ FMinus M) (K : ℕ) (hK1 : 1 ≤ K) (hKN : K ≤ M.N) :
    ∀ x : S, Jstar M K x = ⨅ (π : Policy M) (_ : π.IsMarkov), J M K π x := by sorry

end BertsekasShreve.BorelFinite
