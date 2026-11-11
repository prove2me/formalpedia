-- Prove2me | Theorems.Thm_ChowFormsCH_lemma_2_3
-- name    : ChowFormsCH.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:59:43.054643+00:00
-- url     : https://prove2.me/theorems/c9ef8118-2bd6-4292-9fe3-f0ad521649b8
-- title:
--   Lemma 2.3 — random linear combinations keep the components of codimension $< s$ (corrected: $d \ge 1$)
-- statement:
--   Let $K$ be algebraically closed, $B\subseteq K$ a finite nonempty set, $d\ge 1$, and $f_1,\dots,f_m\in K[x_1,\dots,x_n]$ polynomials of degree at most $d$. Let $g_1,\dots,g_{n+1}$ be linear combinations of $f_1,\dots,f_m$ whose coefficients are picked independently and uniformly from $B$. Then with probability at least
--   $$
--   1-\frac{(n+1)\,d^{\,n}}{|B|}
--   $$
--   the following holds: for each $s\in\{1,\dots,n+1\}$, every irreducible component of $V(g_1,\dots,g_s)$ of codimension less than $s$ is an irreducible component of $V(f_1,\dots,f_m)$; and $V(g_1,\dots,g_{n+1})=V(f_1,\dots,f_m)$.
--
--   The same holds in the projective setting: for forms $f_1,\dots,f_m\in K[x_0,\dots,x_n]$ of degree $d$, with varieties and codimensions taken in $\mathbb P^n$, with the same bound.
--
--   This is the tool that replaces arbitrarily many defining equations by $n+1$ random ones without losing the components of small codimension; Lemma 4.7 applies its projective form.
--
--   **Formalization Note** The index $s$ is 0-based in Lean ($g_0,\dots,g_s$ are $s+1$ combinations). Codimension less than $s+1$ is expressed through topological Krull dimension: $n<\dim Z+(s+1)$ in $K^n$, and $n+1<\dim Z+(s+1)$ in the punctured-cone model of $\mathbb P^n$.
--
--   Differences from the source:
--   - correction: polynomials of degree at most d, any d ≥ 0 → 1 ≤ d; reason: false at d = 0: n = 1, m = 1, f₁ = 1, B = {0}: every g_s = 0, so V(g₁, g₂) = A¹ ≠ ∅ = V(f₁) while the bound is 1 − 2·0¹/1 = 1 (the projective version fails the same way with the form f₁ = 1 of degree 0)
--   - encoding: a field F, varieties over its algebraic closure → an algebraically closed field K (of Type); reason: an instance over F is an instance over K = F̄, with the same varieties
--   - encoding: B ⊆ F a finite set → B a finite nonempty subset of K; reason: uniform sampling from B presupposes B ≠ ∅
--   - reading: The analogous result in the projective setting also holds → forms f₁, …, f_m ∈ K[x₀, …, xₙ] all of degree d, varieties and codimension in P^n, same bound (n+1)d^n; reason: the combinations g_s must be forms to define projective varieties; this is the form Lemma 4.7 uses
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), Lemma 2.3, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_ChowFormsCH_comps
import Definitions.Def_ChowFormsCH_IsSqfPart

set_option autoImplicit false

namespace ChowFormsCH

/-- **Lemma 2.3** (Andrews–Garg–Oliveira–Schost, *Some algebraic and geometric computations in CH
via Chow forms*, arXiv:2611.05289, held version, sha256 75e796c6…, p.9), corrected: `d ≥ 1`.

Affine part: let `B ⊆ K` be finite, `f₁, …, f_m ∈ K[x₁, …, xₙ]` of degree at most `d`, and
`g_s = Σ_l a_{s,l} f_l` (`s = 1, …, n+1`) with coefficients `a_{s,l}` independent and uniform in `B`.
With probability at least `1 − (n+1)d^n/|B|`: for each `s`, every irreducible component of
`V(g₁, …, g_s)` of codimension less than `s` is a component of `V(f₁, …, f_m)`, and
`V(g₁, …, g_{n+1}) = V(f₁, …, f_m)`. Projective part ("The analogous result in the projective setting
also holds"): the same for forms `f_l ∈ K[x₀, …, xₙ]` of degree `d`, with varieties and codimension
in `P^n`.

**Formalization Note** `K` is algebraically closed (an instance over a field `F` is an instance over
`F̄`). The index `s : Fin (n+1)` is 0-based: `V(g₀, …, g_s)` is cut out by `s + 1` combinations and
"codimension less than `s + 1`" in `Kⁿ` is `n < dim Z + (s + 1)`; in `P^n` (punctured cone,
dimension shifted by one) it is `n + 1 < dim Z + (s + 1)`. The coefficient vector is
`a : Fin (n+1) × Fin m → K`. -/
theorem lemma_2_3 {K : Type} [Field K] [IsAlgClosed K] (B : Finset K) (hB : B.Nonempty)
    (n m d : ℕ) (hd : 1 ≤ d) :
    (∀ f : Fin m → MvPolynomial (Fin n) K, (∀ l, (f l).totalDegree ≤ d) →
      (1 : ℝ) - ((n + 1 : ℕ) : ℝ) * (d : ℝ) ^ n / (B.card : ℝ) ≤
        unifProb B (fun a : Fin (n + 1) × Fin m → K =>
          (∀ s : Fin (n + 1), ∀ Z ∈ comps (zeroSet
                {p | ∃ t : Fin (n + 1), t ≤ s ∧ p = ∑ l : Fin m, a (t, l) • f l}),
              (n : WithBot ℕ∞) < topologicalKrullDim Z + (((s : ℕ) + 1 : ℕ) : WithBot ℕ∞) →
              Z ∈ comps (zeroSet (Set.range f))) ∧
          zeroSet (Set.range fun t : Fin (n + 1) => ∑ l : Fin m, a (t, l) • f l)
            = zeroSet (Set.range f))) ∧
    (∀ f : Fin m → MvPolynomial (Fin (n + 1)) K, (∀ l, (f l).IsHomogeneous d) →
      (1 : ℝ) - ((n + 1 : ℕ) : ℝ) * (d : ℝ) ^ n / (B.card : ℝ) ≤
        unifProb B (fun a : Fin (n + 1) × Fin m → K =>
          (∀ s : Fin (n + 1), ∀ Z ∈ comps (projZero
                {p | ∃ t : Fin (n + 1), t ≤ s ∧ p = ∑ l : Fin m, a (t, l) • f l}),
              ((n + 1 : ℕ) : WithBot ℕ∞) < topologicalKrullDim Z + (((s : ℕ) + 1 : ℕ) : WithBot ℕ∞) →
              Z ∈ comps (projZero (Set.range f))) ∧
          projZero (Set.range fun t : Fin (n + 1) => ∑ l : Fin m, a (t, l) • f l)
            = projZero (Set.range f))) := by sorry

end ChowFormsCH
