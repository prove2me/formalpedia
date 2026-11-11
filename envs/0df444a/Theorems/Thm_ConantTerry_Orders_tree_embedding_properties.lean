-- Prove2me | Theorems.Thm_ConantTerry_Orders_tree_embedding_properties
-- name    : ConantTerry.Orders.tree_embedding_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:32:22.770259+00:00
-- url     : https://prove2.me/theorems/7a35760f-b0e0-4527-aa9e-60af5c60fd52
-- title:
--   Proposition 2.2 — prefix reflection, composition, node preservation and extension
-- statement:
--   Write $B_{<s}$ and $B_{\le s}$ for the strict and inclusive truncations of the binary-word tree. All heights in the following four assertions are positive integers.
--
--   1. If $\phi:B_{<s}\to B_{<t}$ is a tree embedding, then
--   $$
--   \sigma\unlhd\tau\iff\phi(\sigma)\unlhd\phi(\tau),
--   $$
--   and $\phi$ is injective.
--   2. If $\phi:B_{<s}\to B_{<t}$ and $\psi:B_{<t}\to B_{<u}$ are tree embeddings, then $\psi\circ\phi$ is a tree embedding. If both maps are proper, their composition is proper. The same assertion holds with inclusive truncations.
--   3. If $\phi:B_{\le s}\to B_{\le t}$ is proper, then
--   $$
--   \phi(B_{<s})\subseteq B_{<t}.
--   $$
--   4. Every tree embedding $\phi:B_{<s}\to B_{<t}$ has a proper extension $\phi^*:B_{\le s}\to B_{\le t}$ agreeing with $\phi$ at every word of length below $s$.
--
--   Together these are the full numbered proposition, including prefix reflection and injectivity, as well as proper composition and extension. They supply the structural interface for function-tree restriction.
--
--   Differences from the source:
--   - encoding: binary words in B_<t, B_≤t and B_t → length-constrained subtypes of List Bool, with false = 0 and true = 1; reason: the empty word, concatenation and initial-segment order are preserved exactly
--   - encoding: proper maps on B_<s = B_≤(s-1), and composition in strict-height notation → IsProperBelow tests length + 1 = s; composition is also stated on WordsAtMost; reason: positive strict heights and inclusive heights differ only by one; inclusive composition is the source composition assertion with all three heights incremented by one
-- source:
--   C. Terry, G. Conant, STOC 2027 submission #1299 (October 2026), p.7, Proposition 2.2(a)–(d); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1299.pdf

import Mathlib
import Definitions.Def_ConantTerry_Orders_tree_embeddings

namespace ConantTerry.Orders

/-- All four parts of Proposition 2.2, p.7. Part (b) includes the same
composition property under both strict and inclusive height conventions. -/
theorem tree_embedding_properties :
    (∀ (s t : ℕ), 1 ≤ s → 1 ≤ t →
      ∀ φ : WordsBelow s → WordsBelow t, IsTreeEmbedding φ →
        (∀ σ τ : WordsBelow s,
          List.IsPrefix σ.val τ.val ↔ List.IsPrefix (φ σ).val (φ τ).val) ∧
        Function.Injective φ) ∧
    ((∀ (s t u : ℕ), 1 ≤ s → 1 ≤ t → 1 ≤ u →
      ∀ (φ : WordsBelow s → WordsBelow t) (ψ : WordsBelow t → WordsBelow u),
        IsTreeEmbedding φ → IsTreeEmbedding ψ →
          IsTreeEmbedding (ψ ∘ φ) ∧
          (IsProperBelow φ → IsProperBelow ψ → IsProperBelow (ψ ∘ φ))) ∧
     (∀ (s t u : ℕ), 1 ≤ s → 1 ≤ t → 1 ≤ u →
      ∀ (φ : WordsAtMost s → WordsAtMost t) (ψ : WordsAtMost t → WordsAtMost u),
        IsTreeEmbedding φ → IsTreeEmbedding ψ →
          IsTreeEmbedding (ψ ∘ φ) ∧
          (IsProperEmbedding φ → IsProperEmbedding ψ → IsProperEmbedding (ψ ∘ φ)))) ∧
    (∀ (s t : ℕ), 1 ≤ s → 1 ≤ t →
      ∀ φ : WordsAtMost s → WordsAtMost t, IsProperEmbedding φ →
        ∀ σ : WordsAtMost s, σ.val.length < s → (φ σ).val.length < t) ∧
    (∀ (s t : ℕ), 1 ≤ s → 1 ≤ t →
      ∀ φ : WordsBelow s → WordsBelow t, IsTreeEmbedding φ →
        ∃ ψ : WordsAtMost s → WordsAtMost t,
          IsProperEmbedding ψ ∧
          ∀ σ : WordsBelow s, (ψ (nodeInclusion σ)).val = (φ σ).val) := by sorry

end ConantTerry.Orders
