-- Prove2me | Theorems.Thm_ApproxDegComp_lemma_20
-- name    : ApproxDegComp.lemma_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:33:46.604942+00:00
-- url     : https://prove2.me/theorems/81edd932-7ddf-42d2-a629-a4fefc917cb8
-- title:
--   Lemma 20 — projectors $E_0,\dots,E_m$ on $\mathbb R^{\mathcal X}$ with a banded structure and $d/3\le\|P_0AP_1\|\le d/2$
-- statement:
--   Let $g:\{0,1\}^m\to\{0,1\}$ be a non-constant Boolean function with $\widetilde{\deg}(g)=d$. Then there exist a nonempty set $\mathcal X\subseteq\{0,1\}^m$ and real orthogonal projectors $E_0,E_1,\dots,E_m$ on $\mathbb R^{\mathcal X}$ such that, with $\tau_k=\min\{k,d\}$ and the real symmetric matrix $A=\sum_{k=0}^m\tau_kE_k$,
--
--   $$\sum_{k=0}^mE_k=I,\qquad 0\preceq A\preceq dI;\tag{8}$$
--
--   $$E_kM_pE_\ell=0\quad\text{if }|k-\ell|>r,\ \text{for every polynomial }p\text{ of degree at most }r;\tag{9}$$
--
--   $$\frac d3\le\lambda=\|P_0AP_1\|\le\frac d2,\qquad P_b=M_{\mathbf 1\{g=b\}}.\tag{10}$$
--
--   Here $\|\cdot\|$ is the operator norm induced by the Euclidean norm and $M_p$ multiplies by $p$ on $\mathcal X$. The matrix $A$ is a "degree operator" adapted to $g$: (9) says multiplication by a degree-$r$ polynomial moves between levels at most $r$ apart, and (10) says $A$ couples $g^{-1}(0)$ and $g^{-1}(1)$ with strength $\Theta(\widetilde{\deg}(g))$.
--
--   **Formalization Note** An orthogonal projector is a symmetric idempotent real matrix; $\preceq$ is the positive-semidefinite order; $\|\cdot\|$ is the $\ell^2$ operator norm (`LiqPremiaEq.opNorm`).
--
--   Differences from the source:
--   - encoding: real orthogonal projector → symmetric idempotent real matrix; reason: the same notion
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), Lemma 20, p.22 (proof Appendix B, pp.45–47)

import Mathlib
import Definitions.Def_ApproxDegComp_approxDeg
import Definitions.Def_ApproxDegComp_mulOp
import Definitions.Def_ApproxDegComp_levelMat
import Definitions.Def_LiqPremiaEq_opNorm

namespace ApproxDegComp

/-- **Lemma 20**, p.22 (proof in Appendix B, pp.45–47).
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Lemma 20, p.22: "Let g : {0, 1}^m → {0, 1} be a non-constant Boolean function with
d̃eg(g) = d. Then there exists a non-empty set X ⊆ {0, 1}^m, real orthogonal projectors
E₀, E₁, …, E_m on ℝ^X and a real symmetric matrix A = Σ_{k=0}^m τ_k E_k where τ_k = min{k, d}
such that they satisfy the following three properties: Σ_{k=0}^m E_k = I, 0 ⪯ A ⪯ dI; (8)
E_k M_p E_ℓ = 0 if |k − ℓ| > r for every polynomial p of degree at most r; (9)
d/3 ≤ λ = ‖P₀AP₁‖ ≤ d/2, where P_b = M_{1{g=b}}. (10)"

**Formalization Note** A real orthogonal projector is a symmetric idempotent real matrix; `A` is
`levelMat E d` (symmetric because each `E_k` is). `‖·‖` is the operator norm induced by the
Euclidean norm (`LiqPremiaEq.opNorm`), as on p.10. `M_p` multiplies by the polynomial `p` in the
`m` bits evaluated at the 0/1 points of `X`; degree is total degree. -/
theorem lemma_20 (m : ℕ) (g : (Fin m → Bool) → Bool) (hg : ∃ x y, g x ≠ g y) (d : ℕ)
    (hd : approxDeg g = d) :
    ∃ X : Finset (Fin m → Bool), X.Nonempty ∧ ∃ E : Fin (m + 1) → Matrix X X ℝ,
      (∀ k, (E k).transpose = E k ∧ E k * E k = E k) ∧
      ∑ k, E k = 1 ∧
      (levelMat E d).PosSemidef ∧ ((d : ℝ) • (1 : Matrix X X ℝ) - levelMat E d).PosSemidef ∧
      (∀ (r : ℕ) (p : MvPolynomial (Fin m) ℝ), p.totalDegree ≤ r →
        ∀ k l : Fin (m + 1), (r : ℤ) < |(k : ℤ) - (l : ℤ)| → E k * mpoly X p * E l = 0) ∧
      (d : ℝ) / 3 ≤ LiqPremiaEq.opNorm (pmat g X false * levelMat E d * pmat g X true) ∧
      LiqPremiaEq.opNorm (pmat g X false * levelMat E d * pmat g X true) ≤ (d : ℝ) / 2 := by sorry

end ApproxDegComp
