-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_nhds_scalar_forall_isOrbitalIntegral_eq_add_mul_of_mem_localCentralizer_of_not_isSquare
-- name    : AutomorphicForm.exists_forall_nhds_scalar_forall_isOrbitalIntegral_eq_add_mul_of_mem_localCentralizer_of_not_isSquare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/4761076e-1ce7-589a-8ef9-de09c74e662e
-- title:
--   Germ expansion of elliptic orbital integrals near a central element
-- statement:
--   Let $K$ be a number field and $v$ a finite place of $K$, i.e. a height-one prime of $\mathcal{O}_K$, with completion $F = K_v$; fix a unit $c \in F^{\times}$, an element $d \in F$ that is not a square, and $u \in \mathrm{GL}_2(F)$ whose matrix is $\begin{pmatrix}0&1\\ d&0\end{pmatrix}$; equip $F$ with a Borel measurable structure and an additive Haar measure $\nu$, and let $\nu_T$ be any measure on $\mathrm{GL}_2(F)$ for the Borel $\sigma$-algebra [`AutomorphicForm.localGLBorel`](def/AutomorphicForm_LocalOrbitalBase.html#L154) of the topological group $\mathrm{GL}_2(F)$. The assertion is that there exist a constant $A \in \mathbb{C}$ and a function $B : \mathrm{GL}_2(F) \to \mathbb{C}$, independent of the test function, with the following two properties. First, for every locally constant, compactly supported $f : \mathrm{GL}_2(F) \to \mathbb{C}$ there is a neighbourhood $W$ of the scalar matrix $z = c \cdot 1$ such that for every $\gamma \in W$ lying in the centralizer subgroup of $u$ and satisfying $\mathrm{IsUnit}(\operatorname{tr}(\gamma)^2 - 4\det(\gamma))$, every Haar measure $\tau$ on the centralizer of $\gamma$ (with its Borel $\sigma$-algebra) whose image under the inclusion into $\mathrm{GL}_2(F)$ is $\nu_T$, and every $I \in \mathbb{C}$ that is an orbital integral of $f$ at $\gamma$ relative to $\tau$ — that is, $I = \int_{\mathrm{GL}_2(F)} f(x^{-1}\gamma x)\, w(x)\, d\mu$ against the Haar measure [`AutomorphicForm.localHaar`](def/AutomorphicForm_LocalOrbitalBase.html#L168) normalised on the compact open set of $g$ with $g$ and $g^{-1}$ entrywise in $\mathcal{O}_v$, for some non-negative measurable compactly supported $w$ with $\int_{Z(\gamma)} w(tx)\, d\tau = 1$ whenever $f(x^{-1}\gamma x) \neq 0$ — one has
--   $$I = A\, f(z) + B(\gamma) \int_k \mathbf{1}_{\{g,\,g^{-1} \text{ integral}\}}(k) \Big( \int_F f\big(z\, k^{-1} n(x) k\big)\, d\nu(x) \Big) d\mu(k), \qquad n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}.$$
--   Secondly, if the pullback of $\nu_T$ along the inclusion of the centralizer of $u$ is a Haar measure on that centralizer, then $A \neq 0$.
--
--   This is the Shalika germ expansion for $\mathrm{GL}_2$ over a non-archimedean local field in a form uniform along an elliptic maximal torus: near a central element $z$ the orbital integrals of a test function at regular elements of the torus $F[u]^{\times}$ are a fixed multiple $A$ of the point term $f(z)$ plus a coefficient $B(\gamma)$ times the averaged regular unipotent term at $z$, with $A$ and $B$ independent of the test function and $A$ non-zero for compatibly normalised measures. It is used by [`AutomorphicForm.exists_germ_forall_isOrbitalIntegral_eq_add_nhds_scalar_of_isLocalTestFn`](thm.html#AutomorphicForm.exists_germ_forall_isOrbitalIntegral_eq_add_nhds_scalar_of_isLocalTestFn) in the local harmonic analysis feeding the trace-formula comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_nhds_scalar_forall_isOrbitalIntegral_eq_add_mul_of_mem_localCentralizer_of_not_isSquare.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain

theorem AutomorphicForm.exists_forall_nhds_scalar_forall_isOrbitalIntegral_eq_add_mul_of_mem_localCentralizer_of_not_isSquare
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (c : (v.adicCompletion K)ˣ)
    (d : v.adicCompletion K) (hd : ¬ IsSquare d)
    (u : GL (Fin 2) (v.adicCompletion K))
    (hu : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![0, 1; d, 0])
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (ν : Measure (v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (νT : @Measure (GL (Fin 2) (v.adicCompletion K)) (AutomorphicForm.localGLBorel K v)) :
    ∃ (A : ℂ) (B : GL (Fin 2) (v.adicCompletion K) → ℂ),
      (∀ (f : GL (Fin 2) (v.adicCompletion K) → ℂ), AutomorphicForm.IsLocalTestFn K v f →
        letI := AutomorphicForm.localGLBorel K v
        ∃ W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
          ∀ γ ∈ W, γ ∈ AutomorphicForm.localCentralizer K v u → AutomorphicForm.IsRegularSemisimple γ →
          ∀ (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ)),
            @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ →
            @Measure.map _ _ (AutomorphicForm.localCentralizerBorel K v γ) (AutomorphicForm.localGLBorel K v)
                Subtype.val τ = νT →
            ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v γ τ f I →
              I = A * f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) +
                B γ * (∫ k, (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ)) k *
                  (∫ x, f (Matrix.GeneralLinearGroup.scalar (Fin 2) c *
                    (k⁻¹ * AutomorphicForm.unipotentGL2 x * k)) ∂ν) ∂(AutomorphicForm.localHaar K v))) ∧
      ((@Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v u)
          (@Measure.comap _ _ (AutomorphicForm.localCentralizerBorel K v u) (AutomorphicForm.localGLBorel K v)
            Subtype.val νT)) → A ≠ 0) := by sorry
