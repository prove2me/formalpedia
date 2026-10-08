-- Prove2me | Theorems.Thm_BertsekasShreve_BorelFinite_prop8_1_markov_equivalent
-- name    : BertsekasShreve.BorelFinite.prop8_1_markov_equivalent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:56:18.437391+00:00
-- url     : https://prove2.me/theorems/bb81576f-b339-491d-80f1-cc9c8ffd8990
-- title:
--   Proposition 8.1 — for a fixed initial state, every policy is matched by a Markov policy
-- statement:
--   Consider the finite horizon Borel model of Definition 8.1 and assume (F⁺) or (F⁻). If $x\in S$ and $\pi'\in\Pi'$ is any policy, then there is a Markov policy $\pi$ such that
--   $$J_{K,\pi}(x)=J_{K,\pi'}(x),\qquad K=1,\dots,N.$$
--
--   The Markov policy may depend on the initial state $x$; a single Markov policy doing as well as $\pi'$ at every $x$ need not exist. The proposition shows that restricting to Markov policies does not change the optimal cost.
--
--   **Formalization Note** "Markov" means that each kernel $\mu_k(\cdot\mid x_0,u_0,\dots,x_k)$ depends on the history only through $x_k$.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 192, Proposition 8.1 (Eq. (11) of Chapter 8)

import Mathlib
import Definitions.Def_BertsekasShreve_BorelFinite_Model
import Definitions.Def_BertsekasShreve_BorelFinite_Policy

namespace BertsekasShreve.BorelFinite

/-- **Proposition 8.1** (p. 192). Under (F⁺) or (F⁻): if `x ∈ S` and `π′ ∈ Π′`, there is a Markov
policy `π` with `J_{K,π}(x) = J_{K,π′}(x)` for `K = 1, …, N`. -/
theorem prop8_1_markov_equivalent {S C W : Type*}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [Nonempty S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [Nonempty C]
    [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [Nonempty W]
    (M : Model S C W)
    (hF : FPlus M ∨ FMinus M) (x : S) (π' : Policy M) :
    ∃ π : Policy M, π.IsMarkov ∧ ∀ K : ℕ, 1 ≤ K → K ≤ M.N → J M K π x = J M K π' x := by sorry

end BertsekasShreve.BorelFinite
