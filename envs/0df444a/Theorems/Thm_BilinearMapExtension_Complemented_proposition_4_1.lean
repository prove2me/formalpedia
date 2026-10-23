-- Prove2me | Theorems.Thm_BilinearMapExtension_Complemented_proposition_4_1
-- name    : BilinearMapExtension.Complemented.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:09:46.081152+00:00
-- url     : https://prove2.me/theorems/e73a8e48-c5ae-4cae-ad63-1b32a026f78f
-- title:
--   Proposition 4.1, p. 3 — the range of a continuous projection is complemented; conversely in a Banach space
-- statement:
--   Let $\mathcal M$ be a subspace (a closed linear manifold) of a normed space $\mathcal X$ over $\mathbb F \in \{\mathbb R, \mathbb C\}$.
--
--   1. If there is a continuous projection $E : \mathcal X \to \mathcal X$ with range $\mathcal R(E) = \mathcal M$, then $\mathcal M$ is complemented, i.e. it has a closed algebraic complement.
--   2. If $\mathcal X$ is a Banach space and $\mathcal M$ is complemented, then there is a continuous projection $E$ with $\mathcal R(E) = \mathcal M$.
--
--   In short, for a subspace of a Banach space,
--   $$\mathcal M \text{ complemented} \iff \mathcal M = \mathcal R(E) \text{ for some } E \in \mathcal B[\mathcal X,\mathcal X],\ E^2 = E.$$
--
--   This is the bridge between the two descriptions of complementation used in the proof of Theorem 5.2: the hypothesis is stated with complements, the construction of the extension uses projections.
--
--   **Formalization Note.** "Subspace" is encoded as a submodule with the hypothesis that it is closed. The first half is stated for normed spaces, the second under `CompleteSpace X`, as on the page. A projection with range $\mathcal M$ is an operator mapping into $\mathcal M$ and fixing $\mathcal M$ pointwise.
-- source:
--   Kubrusly, On extensions of bilinear maps, arXiv:2110.03102v2, p. 3, Proposition 4.1

import Mathlib
import Definitions.Def_BilinearMapExtension_Complemented_Setting

namespace BilinearMapExtension.Complemented

/-- Proposition 4.1, p. 3. -/
theorem proposition_4_1 {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (S : Submodule 𝕜 X) (hS : IsClosed (S : Set X)) :
    ((∃ E : X →L[𝕜] X, IsProjectionOnto E S) → IsComplementedSubspace S) ∧
    ([CompleteSpace X] → IsComplementedSubspace S → ∃ E : X →L[𝕜] X, IsProjectionOnto E S) := by sorry

end BilinearMapExtension.Complemented
