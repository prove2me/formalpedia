-- Prove2me | Theorems.Thm_ConantTerry_Orders_restrict_tree
-- name    : ConantTerry.Orders.restrict_tree
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T06:32:48.083089+00:00
-- url     : https://prove2.me/theorems/5bf729ab-31e3-492d-b944-3e7bd5507bf4
-- title:
--   Proposition 2.3 — restriction along a proper embedding
-- statement:
--   Let $X,Y$ be arbitrary sets, $f:X\times Y\to[0,1]$, $s,t\ge1$ and $\delta>0$. Suppose $(x_\sigma)_{\sigma\in B_{<t}}$, $(y_\eta)_{\eta\in B_t}$ and $(r_\sigma)_{\sigma\in B_{<t}}$ form a $(t,\delta)$-tree for $f$. If $\phi:B_{\le s}\to B_{\le t}$ is a proper tree embedding, then
--   $$
--   (x_{\phi(\sigma)})_{\sigma\in B_{<s}},\qquad
--   (y_{\phi(\eta)})_{\eta\in B_s},\qquad
--   (r_{\phi(\sigma)})_{\sigma\in B_{<s}}
--   $$
--   form an $(s,\delta)$-tree for $f$.
--
--   This result transfers the original labels and thresholds without scale loss. It supports the monotonicity and subtree restrictions used in Section 3.
--
--   Differences from the source:
--   - encoding: binary words in B_<t, B_≤t and B_t → length-constrained subtypes of List Bool, with false = 0 and true = 1; reason: the empty word, concatenation and initial-segment order are preserved exactly
--   - encoding: f and thresholds take values in [0,1] → f and thresholds take values in the real subtype Set.Icc 0 1; reason: subtype membership enforces precisely the source range without added regularity assumptions
--   - encoding: the sequences x_φ(σ), y_φ(η), r_φ(σ) are well-defined restrictions → existential subtype maps nodes and leaves whose underlying words equal φ, with the pulled-back tree condition; reason: the equality constraints uniquely determine both maps and all labels; their existence expresses only the well-definedness of the source conclusion
-- source:
--   C. Terry, G. Conant, STOC 2027 submission #1299 (October 2026), p.8, Proposition 2.3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1299.pdf

import Mathlib
import Definitions.Def_ConantTerry_Orders_function_tree
import Definitions.Def_ConantTerry_Orders_tree_embeddings

namespace ConantTerry.Orders

/-- Proposition 2.3, p.8. The two subtype maps have precisely the words
specified by φ: they are the canonical restrictions, not new label choices. -/
theorem restrict_tree {X : Type*} {Y : Type*}
    (f : X × Y → Set.Icc (0 : ℝ) 1) (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t)
    (δ : ℝ) (hδ : 0 < δ)
    (x : WordsBelow t → X) (y : WordsAt t → Y)
    (r : WordsBelow t → Set.Icc (0 : ℝ) 1)
    (hTree : IsFunctionTree f t δ x y r)
    (φ : WordsAtMost s → WordsAtMost t) (hφ : IsProperEmbedding φ) :
    ∃ (nodes : WordsBelow s → WordsBelow t) (leaves : WordsAt s → WordsAt t),
      (∀ σ, (nodes σ).val = (φ (nodeInclusion σ)).val) ∧
      (∀ η, (leaves η).val = (φ (leafInclusion η)).val) ∧
      IsFunctionTree f s δ (x ∘ nodes) (y ∘ leaves) (r ∘ nodes) := by sorry

end ConantTerry.Orders
