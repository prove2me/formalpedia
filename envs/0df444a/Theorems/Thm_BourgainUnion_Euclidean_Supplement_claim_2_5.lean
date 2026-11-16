-- Prove2me | Theorems.Thm_BourgainUnion_Euclidean_Supplement_claim_2_5
-- name    : BourgainUnion.Euclidean.Supplement.claim_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:33:40.8741+00:00
-- url     : https://prove2.me/theorems/07ecbb9e-3b51-4a55-bf12-ed858561dcb7
-- title:
--   Claim 2.5 — a 1-terminal embedding for a 2-strongly Euclidean set
-- statement:
--   Let $(X,d)$ be a metric space and let $V\subseteq X$ be nonempty and 2-strongly Euclidean in $X$. Then there is a **1-terminal embedding** $\varphi:X\to\ell_2$ for $V$: $\varphi$ is $1$-Lipschitz on all of $X$, and
--   $$\|\varphi(u)-\varphi(x)\|\ge d(u,x)\qquad(u\in V,\ x\in X),$$
--   so $\varphi$ preserves every distance from a point of $V$.
--
--   With Theorem 2.7 at $D=1$, this claim gives Theorem 1.1.
--
--   Differences from the source:
--   - generalization: a metric space X that is finite (the standing convention of §2.1, p. 5) → an arbitrary metric space X; reason: the source proof is pointwise in x, y ∈ X and never uses finiteness; finite X is a special case
--   - encoding: V ∪ S Euclidean for every 2-element S ⊆ X → TwoStrong V: V Euclidean and V ∪ {x, y} Euclidean for all x, y ∈ X (x = y allowed); reason: equivalent: V ∪ {x} ⊆ V ∪ {x, y}, and when X has fewer than two points every subset is Euclidean
--   - encoding: real ℓ₂ → square-summable real sequences H2 = lp (fun _ : ℕ => ℝ) 2; reason: H2 is real ℓ₂, the published target of the base mission
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 6, §2.2, Claim 2.5 (Definition 2.3, p. 5)

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_EmbeddingModel
import Definitions.Def_BourgainUnion_Euclidean_Supplement_StrongModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean.Supplement

open BourgainUnion.Euclidean

/-- Claim 2.5, p. 6: a nonempty 2-strongly Euclidean subset has a 1-terminal embedding. -/
theorem claim_2_5 {X : Type*} [MetricSpace X] (V : Set X) (hV : V.Nonempty)
    (h2 : TwoStrong V) : ∃ φ : X → H2, Terminal V 1 φ := by sorry

end BourgainUnion.Euclidean.Supplement
