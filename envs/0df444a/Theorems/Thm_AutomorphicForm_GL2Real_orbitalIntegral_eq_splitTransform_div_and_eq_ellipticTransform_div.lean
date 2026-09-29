-- Prove2me | Theorems.Thm_AutomorphicForm_GL2Real_orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div
-- name    : AutomorphicForm.GL2Real.orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/6573e71b-e6cf-5333-b702-be5f68db376c
-- title:
--   Orbital integrals at split and elliptic elements of GL₂(ℝ)
-- statement:
--   Let $f:GL_2(\mathbb{R})\to\mathbb{C}$ be continuous with compact support, and let $\mu$ be a Haar measure on $GL_2(\mathbb{R})$ for its Borel $\sigma$-algebra. Write $S$ for the set of $g\in GL_2(\mathbb{R})$ that factor as $\begin{pmatrix} b_1 & b_1x\\ 0 & b_2\end{pmatrix}k$ with $b_1,b_2\in[1,e]$, $x\in[0,1]$ and $k$ in the subgroup `rowIsometrySubgroup₀ ℝ`. Two assertions are made. (Split) For $a_1,a_2$ with $a_1a_2\neq 0$ and $a_1\neq a_2$, for every Haar measure $\tau$ on the centraliser of $\gamma=\mathrm{diag}(a_1,a_2)$ (Borel $\sigma$-algebra), and for every $I\in\mathbb{C}$ which is an orbital integral of $f$ at $\gamma$ relative to $\mu,\tau$ — that is, $I=\int f(x^{-1}\gamma x)w(x)\,d\mu(x)$ for some non-negative measurable $w$ of compact support with $\int_{Z(\gamma)} w(tx)\,d\tau(t)=1$ whenever $f(x^{-1}\gamma x)\neq 0$ — one has $I=\bigl(\mu(S)/\tau(S_A)\bigr)\cdot \mathrm{splitTransform}(f)(a_1,a_2)/\bigl(2|a_1-a_2|\bigr)$, where $S_A$ consists of the centraliser elements whose $(0,0)$ and $(1,1)$ entries both lie in $[1,e]$, and $\mathrm{splitTransform}$ is $(2\pi)^{-1}\int_0^{2\pi}\!\int_{\mathbb{R}} f\bigl(k_\vartheta\,\begin{pmatrix}a_1&u\\0&a_2\end{pmatrix}k_\vartheta^{-1}\bigr)\,du\,d\vartheta$ with $k_\vartheta$ the rotation by $\vartheta$. (Elliptic) For $r>0$ and $\sin\theta\neq0$, for $\gamma=r\,k_\theta$, for every Haar measure $\tau$ on its centraliser and every such orbital integral value $I$, one has $I=\bigl(\mu(S)/\tau(S_B)\bigr)\cdot \mathrm{ellipticTransform}(f)(r,\theta)/\bigl(4\sin^2\theta\bigr)$, where $S_B$ consists of the centraliser elements of determinant in $[1,e^2]$, and $\mathrm{ellipticTransform}(f)(r,\theta)$ equals $4\sin^2\theta$ times $\int_{y>0}\int_{x\in\mathbb{R}} \bigl(f(n\gamma n^{-1})+f(n\gamma' n^{-1})\bigr)y^{-2}\,dx\,dy$ with $n=\begin{pmatrix} y& x\\0&1\end{pmatrix}$ and $\gamma'=r\,k_{-\theta}$.
--
--   This is the archimedean orbital integral computation for $GL_2$: at a regular split element the orbital integral is the integral of $f$ over the conjugates of the upper triangular elements with fixed diagonal, divided by $2|a_1-a_2|$, and at an elliptic element it is the corresponding integral over the upper half-plane, the normalisation-dependence being carried entirely by the ratio of the masses of a fixed box in $GL_2(\mathbb{R})$ and of a fixed box in the centraliser. It feeds the results on vanishing and on the asymptotics of orbital integrals at real places used in the comparison of twisted orbital integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_GL2Real_orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real

theorem AutomorphicForm.GL2Real.orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div
    (f : GL (Fin 2) ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (μ : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ)) (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μ) :
    (∀ (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0), a₁ ≠ a₂ →
      ∀ (τ : @Measure (Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ)))
          (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h))),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h)) τ →
        ∀ I : ℂ, IsOrbitalIntegralOn ℝ μ (upperTriangular a₁ a₂ 0 h) τ f I →
          I = (((μ {g | ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1),
                  ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ k : rowIsometrySubgroup₀ ℝ,
                  (g : Matrix (Fin 2) (Fin 2) ℝ) =
                    !![b₁, b₁ * x; 0, b₂] * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)}).toReal /
                (τ {t | ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ∈ Set.Icc (1 : ℝ) (Real.exp 1) ∧
                  ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ∈ Set.Icc (1 : ℝ) (Real.exp 1)}).toReal :
                ℝ) : ℂ) *
              splitTransform f a₁ a₂ / ((2 * |a₁ - a₂| : ℝ) : ℂ)) ∧
    (∀ (r θ : ℝ) (hr : 0 < r), Real.sin θ ≠ 0 →
      ∀ (τ : @Measure (Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)))
          (centralizerBorel ℝ (ellipticElt r θ hr))),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (ellipticElt r θ hr)) τ →
        ∀ I : ℂ, IsOrbitalIntegralOn ℝ μ (ellipticElt r θ hr) τ f I →
          I = (((μ {g | ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1),
                  ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ k : rowIsometrySubgroup₀ ℝ,
                  (g : Matrix (Fin 2) (Fin 2) ℝ) =
                    !![b₁, b₁ * x; 0, b₂] * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)}).toReal /
                (τ {t | Matrix.det ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) ∈
                  Set.Icc (1 : ℝ) (Real.exp 2)}).toReal : ℝ) : ℂ) *
              ellipticTransform f r θ / (4 * Real.sin θ ^ 2 : ℂ)) := by sorry
