-- Prove2me | Theorems.Thm_AutomorphicForm_GL2Real_exists_ne_zero_tendsto_ellipticTransform_entrySlice_div_sin_sub_div_nhdsWithin_Ioi
-- name    : AutomorphicForm.GL2Real.exists_ne_zero_tendsto_ellipticTransform_entrySlice_div_sin_sub_div_nhdsWithin_Ioi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/ad0f8e55-2baa-5cac-ba12-14e9c397975b
-- title:
--   Harish-Chandra jump formula at the elliptic torus of GL₂(ℝ)
-- statement:
--   There is a real constant $C \neq 0$, quantified outermost and hence independent of all the data below, with the following property. Let $P$ be a type carrying a normed additive group and a real normed space structure, and let $\Phi \colon (\mathrm{Fin}\,2 \to \mathrm{Fin}\,2 \to \mathbb{R}) \times P \to \mathbb{C}$ be $C^\infty$ over $\mathbb{R}$ and compactly supported, with $\mathrm{tsupport}\,\Phi$ contained in the set of pairs $q$ whose matrix coordinate has unit determinant. Let $p \in P$ and $r > 0$. Write $f = \mathrm{entrySlice}\,\Phi\,p$, the function on $\mathrm{GL}_2(\mathbb{R})$ sending $g$ to $\Phi(g, p)$, and for $\theta \in \mathbb{R}$ set $$\mathrm{ellipticTransform}(f, r, \theta) = 4\sin^2\theta \int_{y>0}\!\int_{x \in \mathbb{R}} \bigl(f(h\, r k_\theta\, h^{-1}) + f(h\, r k_{-\theta}\, h^{-1})\bigr)\,\frac{dx\,dy}{y^2},$$ where $h = \begin{pmatrix} y & x \\ 0 & 1\end{pmatrix}$ and $r k_\theta = \begin{pmatrix} r\cos\theta & r\sin\theta \\ -r\sin\theta & r\cos\theta \end{pmatrix}$. Then there exists $L \in \mathbb{C}$ such that, as $\theta \to 0$ within $(0,\infty)$, the quotient $\mathrm{ellipticTransform}(f,r,\theta)/(2\sin\theta)$ tends to $L$, and $\bigl(\mathrm{ellipticTransform}(f,r,\theta)/(2\sin\theta) - L\bigr)/\theta$ tends to $C \cdot \Phi(r \cdot 1, p)$, the value of $\Phi$ at the scalar matrix $r\,\mathrm{Id}$ and the parameter $p$.
--
--   This is Harish-Chandra's limit (jump) formula for $\mathrm{GL}_2(\mathbb{R})$ at the fundamental, elliptic Cartan subgroup: the orbital integral of a smooth compactly supported test function over the regular elliptic class of $rk_\theta$, normalised by the square root $2\sin\theta$ of the Weyl discriminant, has a one-sided limit at $\theta = 0$ and a one-sided derivative there equal to a universal non-zero multiple of the value of the test function at the scalar $r\,\mathrm{Id}$. It is used in the arguments that force orbital integrals at scalars to vanish, and thence in the comparison of twisted and ordinary orbital integrals at scalar elements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_GL2Real_exists_ne_zero_tendsto_ellipticTransform_entrySlice_div_sin_sub_div_nhdsWithin_Ioi.lean

import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real

theorem AutomorphicForm.GL2Real.exists_ne_zero_tendsto_ellipticTransform_entrySlice_div_sin_sub_div_nhdsWithin_Ioi :
    ∃ C : ℝ, C ≠ 0 ∧
      ∀ (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ),
        ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
        tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))} →
        ∀ (p : P) (r : ℝ), 0 < r →
          ∃ L : ℂ,
            Filter.Tendsto (fun θ : ℝ => ellipticTransform (entrySlice Φ p) r θ / (2 * Real.sin θ : ℂ))
              (nhdsWithin 0 (Set.Ioi 0)) (nhds L) ∧
            Filter.Tendsto
              (fun θ : ℝ => (ellipticTransform (entrySlice Φ p) r θ / (2 * Real.sin θ : ℂ) - L) / (θ : ℂ))
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds ((C : ℂ) * Φ (Matrix.of.symm (r • (1 : Matrix (Fin 2) (Fin 2) ℝ)), p))) := by sorry
