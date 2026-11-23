-- Prove2me | Theorems.Thm_CubicNewton_Nonconvex_Supplement_lemma_9
-- name    : CubicNewton.Nonconvex.Supplement.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:13:17.482847+00:00
-- url     : https://prove2.me/theorems/51dee5c3-5799-4711-818a-ed489d716e85
-- title:
--   Lemma 9 — perturbation limit points minimize the cubic subproblem
-- statement:
--   Let $H$ be a symmetric operator on $\mathbb R^n$ ($n\ge1$) with an orthonormal eigenbasis $b_1,\dots,b_n$ and eigenvalues $\lambda_1\ge\dots\ge\lambda_n$, let $M>0$, and let $\tilde g_i=\langle b_i,g\rangle$ be the coordinates of $g$ in this basis. Assume $\tilde g_n=0$. For $\epsilon\ne0$ put $g(\epsilon)=g+\epsilon b_n$ (in the eigenbasis, $\tilde g+\epsilon e_n$), and let $r^*(\epsilon)$ be the solution of equation (5.5) for $g(\epsilon)$,
--   $$r^2=\sum_{i=1}^n\frac{\langle b_i,g(\epsilon)\rangle^2}{(\lambda_i+\frac M2r)^2},\qquad r>\frac2M(-\lambda_n)_+ .$$
--   Then every limit point of the trajectory
--   $$h(g(\epsilon);r^*(\epsilon))=-\Big(H+\frac{Mr^*(\epsilon)}2I\Big)^{-1}g(\epsilon),\qquad\epsilon\to0,$$
--   is a global minimizer in $h$ of $v_u(g;h)=\langle g,h\rangle+\frac12\langle Hh,h\rangle+\frac M6\|h\|^3$. This handles the degenerate case $\tilde g_n=0$, where the explicit formula for the minimizer breaks down.
--
--   Differences from the source:
--   - encoding: eigenvalues λ_1 ≥ … ≥ λ_n with eigenvectors, e_n the n-th coordinate vector of the eigenbasis → OrthonormalBasis b indexed by Fin (n+1) with H(b i) = λ_i b i, λ antitone, b (Fin.last n) in the role of e_n; reason: the n-th coordinate needs n ≥ 1; same instances
--   - encoding: r*(ε) the solution of (5.5) with r ≥ (2/M)(−λ_n)_+ → any function r* with, for ε ≠ 0, r*(ε) > (2/M)(−λ_n)_+ solving (5.5); reason: for ε ≠ 0 the solution lies in the interior (p. 200); the boundary is not a solution because its n-th term is ε²/0 = +∞, while Lean's x/0 = 0 would admit spurious boundary roots
--   - encoding: limit point of the trajectory as ε → 0; g(ε) = g̃ + εe_n → cluster point (MapClusterPt) along ε → 0, ε ≠ 0; g + ε b_n in the original coordinates; reason: same objects
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 200, Lemma 9 (with (5.5), p. 199)

import Mathlib
import Definitions.Def_CubicNewton_Nonconvex_Supplement_CubicDual

open Filter Topology
open scoped RealInnerProductSpace

namespace CubicNewton.Nonconvex.Supplement

/-- Nesterov–Polyak 2006, Lemma 9, p. 200. Let `b₁, …, bₙ` be an orthonormal eigenbasis of the
symmetric operator `H` with eigenvalues `λ₁ ≥ ⋯ ≥ λₙ` (here indexed by `Fin (n+1)`, the last
index playing the role of `n`), and let `g̃_i = ⟨b_i, g⟩` be the coordinates of `g` in this
basis, with `g̃ₙ = 0`. For `ε ≠ 0` put `g(ε) = g + ε bₙ` and let `r*(ε)` be the solution of the
secular equation (5.5) for `g(ε)`,
`r² = Σ_i ⟨b_i, g(ε)⟩² / (λ_i + M r/2)²`, `r > (2/M)(−λₙ)₊`
(for `ε ≠ 0` the solution lies in the interior of the domain, p. 200). Then every limit point, as
`ε → 0` through nonzero values, of the trajectory `h(g(ε); r*(ε)) = −(H + (M r*(ε)/2) I)⁻¹ g(ε)`
is a global minimizer of `h ↦ v_u(g; h)`. -/
theorem lemma_9 {n : ℕ} (g : EuclideanSpace ℝ (Fin (n + 1)))
    (H : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (M : ℝ) (hM : 0 < M)
    (b : OrthonormalBasis (Fin (n + 1)) ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    (lam : Fin (n + 1) → ℝ) (hb : ∀ i, H (b i) = lam i • b i) (hlam : Antitone lam)
    (hgn : ⟪b (Fin.last n), g⟫ = 0)
    (rstar : ℝ → ℝ)
    (hr : ∀ ε : ℝ, ε ≠ 0 →
      2 / M * max (-lam (Fin.last n)) 0 < rstar ε ∧
      rstar ε ^ 2 = ∑ i, ⟪b i, g + ε • b (Fin.last n)⟫ ^ 2 / (lam i + M * rstar ε / 2) ^ 2)
    (p : EuclideanSpace ℝ (Fin (n + 1)))
    (hp : MapClusterPt p (𝓝[≠] (0 : ℝ))
      (fun ε => hDir (g + ε • b (Fin.last n)) H M (rstar ε))) :
    ∀ h : EuclideanSpace ℝ (Fin (n + 1)), vu g H M p ≤ vu g H M h := by sorry

end CubicNewton.Nonconvex.Supplement
