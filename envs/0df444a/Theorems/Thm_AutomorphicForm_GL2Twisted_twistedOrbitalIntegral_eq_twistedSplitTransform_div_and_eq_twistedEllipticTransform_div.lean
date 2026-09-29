-- Prove2me | Theorems.Thm_AutomorphicForm_GL2Twisted_twistedOrbitalIntegral_eq_twistedSplitTransform_div_and_eq_twistedEllipticTransform_div
-- name    : AutomorphicForm.GL2Twisted.twistedOrbitalIntegral_eq_twistedSplitTransform_div_and_eq_twistedEllipticTransform_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/480de90d-7691-5a2d-8cc3-c1772ebddfb0
-- title:
--   Twisted orbital integrals on GL₂(ℂ): split and elliptic cases
-- statement:
--   Let $\varphi : GL_2(\mathbb{C}) \to \mathbb{C}$ be continuous with compact support, and let $\mu$ be a Haar measure for the Borel $\sigma$-algebra on $GL_2(\mathbb{C} \otimes_{\mathbb{R}} \mathbb{R})$; throughout, elements of $GL_2(\mathbb{C} \otimes_{\mathbb{R}} \mathbb{R})$ are read as complex matrices through the entrywise isomorphism induced by $\mathbb{C} \otimes_{\mathbb{R}} \mathbb{R} \cong \mathbb{C}$, the twist $\sigma$ is the entrywise map induced by complex conjugation, and $S$ denotes the set of $g$ whose image matrix has the form $\begin{pmatrix} b_1 & b_1 v \\ 0 & b_2\end{pmatrix} k$ with $b_1, b_2 \in [1, e]$ real, $v \in \mathbb{C}$ with $\mathrm{Re}\,v, \mathrm{Im}\,v \in [0,1]$, and $k$ in the subgroup of $GL_2(\mathbb{C})$ of matrices $k$ with $\|\det k\| = 1$ whose rows act isometrically, i.e. $\|x k_{00} + y k_{10}\|^2 + \|x k_{01} + y k_{11}\|^2 = \|x\|^2 + \|y\|^2$ for all $x, y$. Two assertions are made. First, for all reals $a_1, a_2 > 0$ with $a_1 \ne a_2$, every $\delta$ whose image matrix is $\mathrm{diag}(\sqrt{a_1}, \sqrt{a_2})$, every Haar measure $\tau$ on the twisted centraliser $\{t : t \delta \sigma(t)^{-1} = \delta\}$ and every $I \in \mathbb{C}$ that is a twisted orbital integral of the transported $\varphi$ at $\delta$ relative to $\mu$ and $\tau$ — that is, $I = \int \varphi(x^{-1} \delta \sigma(x)) w(x)\, d\mu$ for some real-valued $w$ satisfying the section condition `IsTwistedSectionFnOn` for $\tau$ — one has $$I = \frac{\mu(S)}{\tau(S_A)} \cdot \frac{\mathrm{tst}(\varphi; a_1, a_2)}{4|a_1 - a_2|},$$ the two measures entering as real numbers, where $S_A$ is the set of $t$ in the twisted centraliser whose image matrix has $(0,0)$ and $(1,1)$ entries with real part in $[1,e]$, and $\mathrm{tst}(\varphi; a_1, a_2) = \mathtt{twistedSplitTransform}$ is $\int_{\mathbb{C}}$ of the unitary average over $k$ of $\varphi(k^{-1} \begin{pmatrix} \sqrt{a_1} & v \\ 0 & \sqrt{a_2}\end{pmatrix} \bar k)\, dv$, the bar denoting entrywise conjugation. Second, for all reals $r > 0$ and $\theta$ with $\sin\theta \ne 0$, every $\delta$ whose image matrix is $\sqrt{r}$ times the rotation by $\theta/2$, every Haar $\tau$ on the twisted centraliser and every such twisted orbital integral value $I$, one has $I = (\mu(S)/\tau(S_B)) \cdot \mathtt{twistedEllipticTransform}\,\varphi\, r\, \theta / (8 \sin^2\theta)$, where $S_B$ is the set of $t$ in the twisted centraliser whose image matrix has determinant with real part in $[1, e^2]$, and the elliptic transform is $4\sin^2\theta$ times the integral over $\rho > 0$ and $u \in \mathbb{C}$ of $\rho^{-1}$ times the sum of the unitary averages of $k \mapsto \varphi(k^{-1}\,\delta_{\mathrm{ell}}(r, \pm\theta, \rho, u)\,\bar k)$.
--
--   This is the archimedean computation of twisted orbital integrals on $GL_2$ over $\mathbb{C}$ with respect to the conjugation twist, at the two types of regular semisimple norm (split with distinct positive eigenvalues, and elliptic), in the normalised form in which the Haar measures on the group and on the twisted centraliser are pinned down by the measures of explicit boxes. It is used by [`AutomorphicForm.exists_contDiff_hasCompactSupport_forall_isTwistedOrbitalIntegralOn_conjAe_imp_eq`](thm.html#AutomorphicForm.exists_contDiff_hasCompactSupport_forall_isTwistedOrbitalIntegralOn_conjAe_imp_eq), where a smooth compactly supported test function with prescribed twisted orbital integrals is produced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_GL2Twisted_twistedOrbitalIntegral_eq_twistedSplitTransform_div_and_eq_twistedEllipticTransform_div.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Twisted
open scoped TensorProduct TensorProduct.RightActions

theorem
AutomorphicForm.GL2Twisted.twistedOrbitalIntegral_eq_twistedSplitTransform_div_and_eq_twistedEllipticTransform_div
    (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (μ : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μ) :
    (∀ (a₁ a₂ : ℝ), 0 < a₁ → 0 < a₂ → a₁ ≠ a₂ →
      ∀ δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
        ((Matrix.GeneralLinearGroup.map
          (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
            (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
          δ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
          !![((Real.sqrt a₁ : ℝ) : ℂ), 0; 0, ((Real.sqrt a₂ : ℝ) : ℂ)] →
        ∀ (τ : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
            (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ →
          ∀ I : ℂ,
            IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μ δ τ
              (fun y => φ
                (Matrix.GeneralLinearGroup.map
                  (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                    (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom y : GL (Fin 2) ℂ)) I →
            I = (((
              (μ {g | ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1),
                  ∃ v : ℂ, v.re ∈ Set.Icc (0 : ℝ) 1 ∧ v.im ∈ Set.Icc (0 : ℝ) 1 ∧
                  ∃ k : AutomorphicForm.WindowedSiegel.rowIsometrySubgroup ℂ,
                  ((Matrix.GeneralLinearGroup.map
                    (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                      (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
                    g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
                    !![(b₁ : ℂ), (b₁ : ℂ) * v; 0, (b₂ : ℂ)] *
                      ((k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)}).toReal /
              (τ {t |
                  (((Matrix.GeneralLinearGroup.map
                    (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                      (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
                    (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ∈
                    Set.Icc (1 : ℝ) (Real.exp 1) ∧
                  (((Matrix.GeneralLinearGroup.map
                    (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                      (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
                    (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1).re ∈
                    Set.Icc (1 : ℝ) (Real.exp 1)}).toReal : ℝ) : ℂ) *
                twistedSplitTransform φ a₁ a₂ / ((4 * |a₁ - a₂| : ℝ) : ℂ))) ∧
    (∀ (r θ : ℝ), 0 < r → Real.sin θ ≠ 0 →
      ∀ δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
        ((Matrix.GeneralLinearGroup.map
          (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
            (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
          δ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
          !![((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ), ((Real.sqrt r * Real.sin (θ / 2) : ℝ) : ℂ);
            ((-(Real.sqrt r * Real.sin (θ / 2)) : ℝ) : ℂ), ((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ)] →
        ∀ (τ : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
            (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ →
          ∀ I : ℂ,
            IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μ δ τ
              (fun y => φ
                (Matrix.GeneralLinearGroup.map
                  (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                    (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom y : GL (Fin 2) ℂ)) I →
            I = (((
              (μ {g | ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1),
                  ∃ v : ℂ, v.re ∈ Set.Icc (0 : ℝ) 1 ∧ v.im ∈ Set.Icc (0 : ℝ) 1 ∧
                  ∃ k : AutomorphicForm.WindowedSiegel.rowIsometrySubgroup ℂ,
                  ((Matrix.GeneralLinearGroup.map
                    (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                      (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
                    g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
                    !![(b₁ : ℂ), (b₁ : ℂ) * v; 0, (b₂ : ℂ)] *
                      ((k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)}).toReal /
              (τ {t | (Matrix.det
                  ((Matrix.GeneralLinearGroup.map
                    (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                      (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
                    (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)).re ∈
                    Set.Icc (1 : ℝ) (Real.exp 2)}).toReal : ℝ) : ℂ) *
                twistedEllipticTransform φ r θ / (8 * Real.sin θ ^ 2 : ℂ))) := by sorry
