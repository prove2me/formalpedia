-- Prove2me | Theorems.Thm_AutomorphicForm_apply_scalar_eq_const_mul_of_isOrbitalIntegralOn_rotation_nhdsGT_of_tendsto_ellipticTransform
-- name    : AutomorphicForm.apply_scalar_eq_const_mul_of_isOrbitalIntegralOn_rotation_nhdsGT_of_tendsto_ellipticTransform
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/3ec8fe26-6887-5afb-b5b7-26ddc3f4d5db
-- title:
--   Harish-Chandra limit formula at a scalar matrix, explicit constant
-- statement:
--   Fix a Haar measure $\mu$ on $GL_2(\mathbb R)$ (carrying the Borel $\sigma$-algebra `glBorelOf ℝ`), a unit $c\in\mathbb R^\times$, a family $\gamma:\mathbb R\to GL_2(\mathbb R)$ with $\gamma(\theta)=c\cdot\begin{pmatrix}\cos\theta&-\sin\theta\\ \sin\theta&\cos\theta\end{pmatrix}$, a further Borel measure $\nu_T$ on $GL_2(\mathbb R)$, and a real $C\neq 0$. Assume the jump relation: for every real normed space $P$ and every smooth compactly supported $\Psi:(\mathrm{Fin}\,2\to\mathrm{Fin}\,2\to\mathbb R)\times P\to\mathbb C$ whose support meets only pairs with invertible first entry-matrix, and all $p\in P$, $r>0$, the quotient $\mathrm{ellipticTransform}(\mathrm{entrySlice}\,\Psi\,p)(r,\theta)/(2\sin\theta)$ has a limit $L$ as $\theta\to 0^+$ and $(\,\cdot\,-L)/\theta\to C\,\Psi(r\cdot 1,p)$; here $\mathrm{ellipticTransform}$ of $h$ is $4\sin^2\theta\int_{y>0}\int_{x\in\mathbb R}\bigl(h(n\,k_{r,\theta}\,n^{-1})+h(n\,k_{r,-\theta}\,n^{-1})\bigr)y^{-2}$, with $n=\begin{pmatrix}y&x\\0&1\end{pmatrix}$ and $k_{r,\theta}=\begin{pmatrix}r\cos\theta&r\sin\theta\\-r\sin\theta&r\cos\theta\end{pmatrix}$, and $\mathrm{entrySlice}\,\Psi\,p(g)=\Psi(g,p)$. Then for every $f:GL_2(\mathbb R)\to\mathbb C$ which is a smooth function of the matrix entries and has compact support, every $\theta_0>0$, every family of Haar measures $\tau_\theta$ on the centralisers of $\gamma(\theta)$ ($0<\theta<\theta_0$) pushing forward along inclusion to $\nu_T$, and every $\Phi:\mathbb R\to\mathbb C$ such that for $0<\theta<\theta_0$ one has $\Phi(\theta)=\int f(x^{-1}\gamma(\theta)x)w(x)\,d\mu$ for some non-negative measurable compactly supported $w$ with $\int_{t}w(tx)\,d\tau_\theta=1$ whenever $f(x^{-1}\gamma(\theta)x)\neq 0$: there are $L_1,L_2\in\mathbb C$ with $\sin\theta\,\Phi(\theta)\to L_1$ and $(\sin\theta\,\Phi(\theta)-L_1)/\theta\to L_2$ as $\theta\to0^+$, with $\nu_T(T)$ of positive real value for $T=\{g:\det g\in[1,e^2]\}$, and $$f(c\cdot 1)=\frac{2}{\bigl(\mu(S)/\nu_T(T)\bigr)\,C}\,L_2,$$ where $S$ is the Iwasawa box $\{g=\begin{pmatrix}b_1&b_1x\\0&b_2\end{pmatrix}k : b_1,b_2\in[1,e],\ x\in[0,1],\ k\in\,$`rowIsometrySubgroup₀ ℝ`$\}$, the measure values being taken as real numbers. No value is asserted for $L_1$.
--
--   This is Harish-Chandra's limit formula on $GL_2(\mathbb R)$ at a scalar element along the elliptic torus, in the explicit form in which the constant relating $f(c\cdot 1)$ to the right derivative $L_2$ of $\sin\theta\,\Phi(\theta)$ is written out in terms of $\mu$, $\nu_T$ and the jump constant $C$. It is used in the comparison of archimedean orbital and twisted orbital integrals at scalar elements, namely by [`AutomorphicForm.isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isNormConjugator_of_neg`](thm.html#AutomorphicForm.isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isNormConjugator_of_neg) and [`AutomorphicForm.isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isRegularSemisimple_of_neg`](thm.html#AutomorphicForm.isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isRegularSemisimple_of_neg).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_apply_scalar_eq_const_mul_of_isOrbitalIntegralOn_rotation_nhdsGT_of_tendsto_ellipticTransform.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.apply_scalar_eq_const_mul_of_isOrbitalIntegralOn_rotation_nhdsGT_of_tendsto_ellipticTransform
    (μ : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
    (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μ)
    (c : ℝˣ)
    (γ : ℝ → GL (Fin 2) ℝ)
    (hγ : ∀ θ : ℝ, ((γ θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (c : ℝ) • !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ])
    (νT : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
    (C : ℝ) (hC : C ≠ 0)
    (hjump : ∀ (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ),
        ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
        tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))} →
        ∀ (p : P) (r : ℝ), 0 < r →
          ∃ L : ℂ,
            Filter.Tendsto (fun θ : ℝ => ellipticTransform (entrySlice Φ p) r θ / (2 * Real.sin θ : ℂ))
              (nhdsWithin 0 (Set.Ioi 0)) (nhds L) ∧
            Filter.Tendsto
              (fun θ : ℝ => (ellipticTransform (entrySlice Φ p) r θ / (2 * Real.sin θ : ℂ) - L) / (θ : ℂ))
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds ((C : ℂ) * Φ (Matrix.of.symm (r • (1 : Matrix (Fin 2) (Fin 2) ℝ)), p)))) :
      ∀ (f : GL (Fin 2) ℝ → ℂ),
        ((∃ F : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
          ∀ g, f g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport f) →
      ∀ (θ₀ : ℝ), 0 < θ₀ →
      ∀ (τ : ∀ θ : ℝ, @Measure (Subgroup.centralizer ({γ θ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ (γ θ))),
        (∀ θ ∈ Set.Ioo 0 θ₀, @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (γ θ)) (τ θ)) →
        (∀ θ ∈ Set.Ioo 0 θ₀, @Measure.map _ _ (centralizerBorel ℝ (γ θ)) (glBorelOf ℝ) Subtype.val (τ θ) = νT) →
      ∀ (Φ : ℝ → ℂ),
        (∀ θ ∈ Set.Ioo 0 θ₀, IsOrbitalIntegralOn ℝ μ (γ θ) (τ θ) f (Φ θ)) →
        ∃ L₁ L₂ : ℂ,
          Filter.Tendsto (fun θ : ℝ => (Real.sin θ : ℂ) * Φ θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds L₁) ∧
          Filter.Tendsto (fun θ : ℝ => ((Real.sin θ : ℂ) * Φ θ - L₁) / (θ : ℂ)) (nhdsWithin 0 (Set.Ioi 0))
            (nhds L₂) ∧
          0 < (νT {g : GL (Fin 2) ℝ | Matrix.det (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 2)}).toReal ∧
          f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
            (((2 : ℝ) /
                ((μ {g : GL (Fin 2) ℝ | ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1),
              ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ k : rowIsometrySubgroup₀ ℝ,
              (g : Matrix (Fin 2) (Fin 2) ℝ) =
                !![b₁, b₁ * x; 0, b₂] * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)}).toReal /
                    (νT {g : GL (Fin 2) ℝ | Matrix.det (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 2)}).toReal *
                  C) : ℝ) : ℂ) * L₂ := by sorry
