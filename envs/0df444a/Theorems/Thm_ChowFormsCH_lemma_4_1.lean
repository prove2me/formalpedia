-- Prove2me | Theorems.Thm_ChowFormsCH_lemma_4_1
-- name    : ChowFormsCH.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:02:06.230194+00:00
-- url     : https://prove2.me/theorems/d824316b-83d7-4db4-b82e-6d7bbe9f91c0
-- title:
--   Lemma 4.1 — the limit varieties $\lim_{t\to\tau} V^p(G)$ are equidimensional of codimension $k$ and contain the codimension-$k$ components of $V(G)$
-- statement:
--   Let $K$ be algebraically closed, $k\le n$, and $G_1,\dots,G_k\in K[x_0,\dots,x_n]$ forms of degrees $d_1,\dots,d_k$. Then:
--
--   1. every irreducible component of $V^p(G_1,\dots,G_k)\subseteq\mathbb P^n\times\mathbb A^1$ has codimension at most $k$;
--   2. the components $W_1,\dots,W_a$ whose projection to $\mathbb A^1$ is surjective have codimension exactly $k$;
--   3. for every $\tau\in K$, $\lim_{t\to\tau}V^p(G_1,\dots,G_k)$ is an equidimensional variety of codimension $k$ in $\mathbb P^n$;
--   4. $\lim_{t\to 0}V^p(G_1,\dots,G_k)\subseteq V(G_1,\dots,G_k)$, and every codimension-$k$ irreducible component of $V(G_1,\dots,G_k)$ is an irreducible component of $\lim_{t\to 0}V^p(G_1,\dots,G_k)$.
--
--   The deformation $(1-t)G_i+tx_i^{d_i}$ thus produces, at $t=0$, an equidimensional subvariety of $V(G)$ of the expected codimension that keeps all components of that codimension; Lemmas 4.6 and 4.7 compute its Chow form.
--
--   **Formalization Note** Codimension $k$ in $\mathbb P^n\times\mathbb A^1$ is topological dimension $n+2-k$ of the model, and codimension $k$ in $\mathbb P^n$ is topological dimension $n-k+1$ of the punctured cone.
--
--   Differences from the source:
--   - encoding: forms over a field F ("the results of Section 4.1 hold over arbitrary fields"), varieties over F̄ → an algebraically closed field K (of Type); reason: an instance over F is an instance over K = F̄, with the same varieties
--   - reading: d_i := deg G_i → G_i homogeneous of degree d_i, the zero form allowed with its formal degree; reason: the zero polynomial is a form of every degree; the deformation needs only the exponent d_i
--   - encoding: an equidimensional variety of codimension k → every irreducible component has codimension k; the empty variety qualifies; reason: the paper's convention: an empty component V_k has Chow form 1 (proof of Theorem 4.9)
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), Lemma 4.1, p.29 (PDF p.31)

import Mathlib
import Definitions.Def_ChowFormsCH_comps
import Definitions.Def_ChowFormsCH_limVar

set_option autoImplicit false

namespace ChowFormsCH

/-- **Lemma 4.1** (Andrews–Garg–Oliveira–Schost, *Some algebraic and geometric computations in CH
via Chow forms*, arXiv:2611.05289, held version, sha256 75e796c6…, p.29). Let `G₁, …, G_k` be forms
of degrees `d₁, …, d_k` in `x₀, …, xₙ`, `k ≤ n`. Every component of `V^p(G₁, …, G_k) ⊆ P^n × A¹` has
codimension at most `k`, and the components `W₁, …, W_a` whose projection to `A¹` is surjective have
codimension exactly `k`. For every `τ`, `lim_{t→τ} V^p(G₁, …, G_k)` is an equidimensional variety of
codimension `k` in `P^n`. Further `lim_{t→0} V^p(G₁, …, G_k) ⊆ V(G₁, …, G_k)`, and every
codimension-`k` component of the latter is an irreducible component of the former.

**Formalization Note** `K` is algebraically closed. Dimensions are topological Krull dimensions of
the models `ProjAff n K` (codimension `k` in `P^n × A¹` is dimension `n + 2 − k`) and `ProjSpace n K`
(codimension `k` in `P^n` is dimension `n − k + 1`). A zero form `G_i` is allowed, with its formal
degree `d_i`. The empty variety counts as equidimensional of codimension `k`. -/
theorem lemma_4_1 {K : Type} [Field K] [IsAlgClosed K] {n k : ℕ} (hk : k ≤ n)
    (G : Fin k → MvPolynomial (Fin (n + 1)) K) (d : Fin k → ℕ)
    (hG : ∀ i, (G i).IsHomogeneous (d i)) :
    (∀ Z ∈ comps (Vp hk G d), ((n + 2 - k : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim Z) ∧
    (∀ Z ∈ comps (Vp hk G d), (∀ τ : K, ∃ p ∈ Z, p.t = τ) →
      topologicalKrullDim Z = ((n + 2 - k : ℕ) : WithBot ℕ∞)) ∧
    (∀ τ : K, IsProjEquidim (limVar hk G d τ) (n - k)) ∧
    limVar hk G d 0 ⊆ projZero (Set.range G) ∧
    (∀ Y ∈ comps (projZero (Set.range G)),
      topologicalKrullDim Y = ((n - k + 1 : ℕ) : WithBot ℕ∞) → Y ∈ comps (limVar hk G d 0)) := by sorry

end ChowFormsCH
