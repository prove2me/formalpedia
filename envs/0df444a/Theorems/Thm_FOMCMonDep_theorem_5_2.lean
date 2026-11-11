-- Prove2me | Theorems.Thm_FOMCMonDep_theorem_5_2
-- name    : FOMCMonDep.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:23:47.133458+00:00
-- url     : https://prove2.me/theorems/6b883cdf-997a-45ad-901b-3b9694090fd1
-- title:
--   Theorem 5.2 (Closure Theorem for Tuples) — $O(|A|^c)$ many $s$-flips, one separating each $k$-tuple from $A$
-- statement:
--   Let $\mathcal C$ be a monadically dependent class of (possibly infinite) graphs, $r\in\mathbb N$ and $k\in\mathbb N$. There are $c,s\in\mathbb N$ such that for every $G\in\mathcal C$ and every finite $A\subseteq V(G)$ there is a set $\mathcal H$ of $O_{\mathcal C,r,k}(|A|^c)$ many $s$-flips of $G$ such that every tuple $\bar v\in(V(G)-A)^k$ has a flip $H\in\mathcal H$ with
--   $$\mathrm{dist}_H(\bar v,A)>r .$$
--
--   The flips here are partition flips with at most $s$ parts, not $s$-definable flips. This is the form of the Closure Theorem used in the proof of Theorem 4.4.
--
--   **Formalization Note** $O_{\mathcal C,r,k}(|A|^c)$ is $a|A|^c+b$ with $a,b$ chosen after $\mathcal C,r,k$. $\mathrm{dist}_H(\bar v,A)$ is the minimum over the entries of $\bar v$ and the elements of $A$.
--
--   Differences from the source:
--   - encoding: a monadically dependent class of possibly infinite graphs (Part I) → AnyGraphClass (members on every vertex type) with MonDepAny; reason: the paper's definition with the witness graph on any type; Part I allows infinite graphs
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), Theorem 5.2, p.18 (PDF 20)

import Mathlib
import Definitions.Def_FOMCMonDep_IsPFlip
import Definitions.Def_FOMCMonDep_MonDepAny

set_option autoImplicit false

namespace FOMCMonDep

/-- **Theorem 5.2 (Closure Theorem for Tuples).** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §5, p.18 (PDF 20); proof p.26 (PDF 28):
"For every monadically dependent graph class 𝒞, radius r ∈ N, and tuple size k ∈ N, there are some c, s ∈ N with the
following property. For every G ∈ 𝒞 and finite set A ⊆ V(G) there is a set ℋ of O_{𝒞,r,k}(|A|^c) many s-flips of G
such that for every tuple v̄ ∈ (V(G) − A)^k there is a flip H ∈ ℋ with dist_H(v̄, A) > r."

**Formalization Note.** Part I (possibly infinite graphs). "s-flips" are `𝒫`-flips with `|𝒫| ⩽ s` (`IsSFlip`), not
`s`-definable flips (p.18: "the conclusion uses non-definable flips"). `ℋ` is a finite set of graphs on `V` with
`|ℋ| ⩽ a · |A|^c + b`, `a, b` after `𝒞, r, k`. `dist_H(v̄, A)` is the minimum over the entries of `v̄` and the
elements of `A`. -/
theorem theorem_5_2 (𝒞 : AnyGraphClass) (h𝒞 : MonDepAny 𝒞) (r k : ℕ) :
    ∃ c s : ℕ, ∃ a b : ℕ, ∀ (V : Type) (G : SimpleGraph V), G ∈ 𝒞 V → ∀ A : Set V, A.Finite →
      ∃ ℋ : Set (SimpleGraph V), ℋ.Finite ∧ ℋ.ncard ≤ a * A.ncard ^ c + b ∧ (∀ H ∈ ℋ, IsSFlip G s H) ∧
        ∀ v : Fin k → V, (∀ i, v i ∉ A) →
          ∃ H ∈ ℋ, ∀ i, ∀ x ∈ A, (r : ℕ∞) < H.edist (v i) x := by sorry

end FOMCMonDep
