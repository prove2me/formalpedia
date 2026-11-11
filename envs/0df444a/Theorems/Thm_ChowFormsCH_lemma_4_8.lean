-- Prove2me | Theorems.Thm_ChowFormsCH_lemma_4_8
-- name    : ChowFormsCH.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:03:11.5342+00:00
-- url     : https://prove2.me/theorems/40fedabc-ca93-47c8-a64f-6d54292f5ac3
-- title:
--   Lemma 4.8 — random coordinates put the affine part in projective Noether position with primitive element $x_{r+1}$
-- statement:
--   Let $K$ be algebraically closed, $W\subseteq\mathbb P^n$ an equidimensional projective variety of dimension $r<n$ and degree $D$, and $B$ a finite nonempty subset of the coefficient subfield of $K$ with $0\notin B$. Let $M\in K^{(n+1)\times(n+1)}$ have entries picked uniformly and independently from $B$, $\phi(\alpha)=M\alpha$, and $W'$ the restriction of $\phi(W)$ to the affine chart $x_0\neq 0$, a subset of $K^n$ with coordinates $x_1,\dots,x_r$ and $x_{r+1},\dots,x_n$. Conditionally on $M$ being invertible, with probability at least
--   $$
--   1-\frac{5\,n\,D}{|B|}
--   $$
--   the variety $W'$ is in projective Noether position, $x_{r+1}$ is a primitive element for $W'$, and the projective closure of $W'$ is exactly $\phi(W)$.
--
--   In Theorem 4.9 this random change of coordinates prepares each $V^\star_k$ for the geometric-resolution computations of Section 3.
--
--   **Formalization Note** The ambient space is $\mathbb P^{r+e}$ with $e\ge 1$. Conditioning is stated without division: the number of invertible matrices satisfying the conclusion is at least $(1-5nD/|B|)$ times the number of invertible matrices.
--
--   Differences from the source:
--   - encoding: a field F, B ⊆ F∖{0} a subset of the coefficient subfield of F, varieties over F̄ → an algebraically closed field K (of Type), B inside its coefficient subfield, B finite and nonempty; reason: an instance over F is an instance over K = F̄; uniform sampling presupposes a finite nonempty B
--   - reading: x_{r+1} is a primitive element for ϕ(W′), where r = dim W → x_{r+1} is a primitive element for W′, with n = r + e, e ≥ 1; reason: W′ is already the affine part of ϕ(W); x_{r+1} exists only for r < n
--   - reading: Suppose M is invertible … With probability at least 1 − 5nD/|B| → #{M invertible satisfying the conclusion} ≥ (1 − 5nD/|B|)·#{M invertible}; reason: the joint reading P(M invertible and conclusion) ≥ 1 − 5nD/|B| is false for W = ∅ (D = 0, the bound is 1, but for B = {1} and n ≥ 1 every M is singular); conditioning is the stronger of the remaining readings
--   - encoding: W′ is in projective Noether position (Definition 3.2) → W′ is an equidimensional affine variety of dimension r with a fiber of cardinality deg W′; reason: Definition 3.2 applies only to equidimensional varieties of dimension m, here r
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), Lemma 4.8, p.33 (PDF p.35)

import Mathlib
import Definitions.Def_ChowFormsCH_comps
import Definitions.Def_ChowFormsCH_affDegree
import Definitions.Def_ChowFormsCH_affTrace
import Definitions.Def_ChowFormsCH_IsPrimitiveY1
import Definitions.Def_ChowFormsCH_IsSqfPart

set_option autoImplicit false

namespace ChowFormsCH

/-- **Lemma 4.8** (Andrews–Garg–Oliveira–Schost, *Some algebraic and geometric computations in CH
via Chow forms*, arXiv:2611.05289, held version, sha256 75e796c6…, p.33). Let `W ⊆ P^n` be an
equidimensional projective variety of degree `D` and dimension `r`, `B` a finite subset of the
coefficient subfield of `K` not containing `0`, and `M ∈ K^{(n+1)×(n+1)}` with entries independent and
uniform in `B`; suppose `M` is invertible and let `ϕ(α) = Mα`. Let `W′` be the restriction of `ϕ(W)`
to the affine chart of points at finite distance. With probability at least `1 − 5nD/|B|`, `W′` is in
projective Noether position and `x_{r+1}` is a primitive element for `W′`; further the projective
closure of `W′` is exactly `ϕ(W)`.

**Formalization Note** `K` is algebraically closed. The ambient space is `P^{r+e}` with `e ≥ 1`
(`n = r + e`): `x_{r+1}` exists only for `r < n`. The chart is `x₀ ≠ 0`, with coordinates
`x₁, …, x_r` (the `x`-block, `Sum.inl`) and `x_{r+1}, …, xₙ` (the `y`-block, `Sum.inr`); `x_{r+1}` is
`y₁`. "Suppose M is invertible" is read as conditioning: the number of matrices that are invertible
and satisfy the conclusion is at least `(1 − 5nD/|B|)` times the number of invertible matrices. -/
theorem lemma_4_8 {K : Type} [Field K] [IsAlgClosed K] {r e : ℕ} [NeZero e]
    (W : Set (ProjSpace (r + e) K)) (hW : IsProjVariety W) (hWeq : IsProjEquidim W r)
    (B : Finset K) (hB : B.Nonempty) (hB0 : (0 : K) ∉ B)
    (hBc : ∀ b ∈ B, IsAlgebraic (⊥ : Subfield K) b) :
    ((1 : ℝ) - 5 * ((r + e : ℕ) : ℝ) * (projDegree W : ℝ) / (B.card : ℝ)) *
        unifProb B (fun M : Fin (r + e + 1) × Fin (r + e + 1) → K =>
          IsUnit (Matrix.of fun i j => M (i, j)).det) ≤
      unifProb B (fun M : Fin (r + e + 1) × Fin (r + e + 1) → K =>
        IsUnit (Matrix.of fun i j => M (i, j)).det ∧
        IsNoetherPosition (affTrace (m := r) (n := e) (linImage (Matrix.of fun i j => M (i, j)) W)) ∧
        IsPrimitiveY1 (affTrace (m := r) (n := e) (linImage (Matrix.of fun i j => M (i, j)) W)) ∧
        projClosure (affTrace (m := r) (n := e) (linImage (Matrix.of fun i j => M (i, j)) W))
          = linImage (Matrix.of fun i j => M (i, j)) W) := by sorry

end ChowFormsCH
