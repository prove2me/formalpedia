-- Prove2me | Theorems.Thm_AutomorphicForm_GL2Real_discreteSeriesPairing_entrySlice_eq_zero_of_weight
-- name    : AutomorphicForm.GL2Real.discreteSeriesPairing_entrySlice_eq_zero_of_weight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/19237702-3d39-5214-8c49-9e0c5eeb240e
-- title:
--   Vanishing of discrete-series pairings for rotation type m
-- statement:
--   Let $P$ be a real normed space, let $m$ be a natural number, and let $\Phi$ be a complex-valued function on pairs $(M,p)$ with $M$ a real $2\times 2$ entry matrix and $p \in P$, assumed $C^\infty$ over $\mathbb{R}$, of compact support, and with $\operatorname{tsupport}\Phi$ contained in the set of pairs whose matrix part has invertible determinant. Write $f_p :=$ `entrySlice` $\Phi\,p$ for the induced function on $GL_2(\mathbb{R})$, namely $f_p(g) = \Phi(g,p)$ with $g$ read as its entry matrix. Assume the two-sided type condition: for all $p$, all $k_1,k_2$ in the subgroup `rowIsometrySubgroup₀ ℝ` of $GL_2(\mathbb{R})$ and all $g$, one has $f_p(k_1 g k_2) = \chi(k_1)\chi(k_2) f_p(g)$, where $\chi$ is the character `archWeightCharℝ` at $(m : \mathbb{Z})$, its values being regarded as units of $\mathbb{C}$. Let $H$ be the split transform of $f_p$, $H(a_1,a_2) = \frac{1}{2\pi}\int_0^{2\pi}\!\int_{\mathbb{R}} f_p\bigl(R_\theta\,\binom{a_1\ u}{0\ a_2}\,R_\theta^{-1}\bigr)\,du\,d\theta$ when $a_1a_2 \neq 0$ and $0$ otherwise, and let $E$ be the elliptic transform, $E(r,\theta) = 4\sin^2\theta \int_{y>0}\int_{\mathbb{R}} \bigl[f_p(n\,e(r,\theta)\,n^{-1}) + f_p(n\,e(r,-\theta)\,n^{-1})\bigr] y^{-2}\,dx\,dy$ for $r>0$, with $n = \binom{y\ x}{0\ 1}$ and $e(r,\theta) = r R_\theta$, and $0$ for $r \le 0$. Then for every $p \in P$ the pairing $$\Lambda_j(r) = \int_0^{\pi} E(r,\theta)\,U_{j-2}(\cos\theta)\,d\theta - \frac{2\pi}{r}\int_{\mathbb{R}} e^{-(j-1)|t|}\bigl(H(re^t, re^{-t}) + (-1)^j H(-re^t, -re^{-t})\bigr)\,dt,$$ with $U$ the Chebyshev polynomial of the second kind, vanishes for every $r>0$ in each of the two cases: for all $j \ge m+2$, and for all $j \ge 2$ with $j+m$ odd.
--
--   This expresses the orthogonality of a function of two-sided rotation type $m$ on $GL_2(\mathbb{R})$ to the characters of the discrete series of lowest weight $j$ when $j \ge m+2$ (the type $m$ then not occurring in the corresponding holomorphic and antiholomorphic series), together with the vanishing at the wrong parity, where both terms of the pairing change sign under the central element $-1$. It is used by [`AutomorphicForm.GL2Real.exists_contDiff_splitTransform_eq_ellipticTransform_eq_of_discreteSeriesPairing`](thm.html#AutomorphicForm.GL2Real.exists_contDiff_splitTransform_eq_ellipticTransform_eq_of_discreteSeriesPairing), which produces smooth compactly supported functions on $GL_2(\mathbb{R})$ with prescribed split and elliptic orbital transforms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_GL2Real_discreteSeriesPairing_entrySlice_eq_zero_of_weight.lean

import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm AutomorphicForm.GL2Real

theorem AutomorphicForm.GL2Real.discreteSeriesPairing_entrySlice_eq_zero_of_weight
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (m : ℕ)
    (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦinv : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))})
    (htype : ∀ (p : P) (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
      entrySlice Φ p ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
        ((archWeightCharℝ (m : ℤ) k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ (m : ℤ) k₂ : ℂˣ) : ℂ) * entrySlice Φ p g) :
    ∀ p : P,
      (∀ j : ℕ, m + 2 ≤ j → ∀ r : ℝ, 0 < r →
        discreteSeriesPairing j (splitTransform (entrySlice Φ p)) (ellipticTransform (entrySlice Φ p)) r = 0) ∧
      (∀ j : ℕ, 2 ≤ j → ¬ 2 ∣ j + m → ∀ r : ℝ, 0 < r →
        discreteSeriesPairing j (splitTransform (entrySlice Φ p)) (ellipticTransform (entrySlice Φ p)) r = 0) := by sorry
