-- Prove2me | Theorems.Thm_AutomorphicForm_exists_nhds_scalar_forall_isOrbitalIntegral_eq_mul_integral_unipotentGL2_conj_of_diagonal
-- name    : AutomorphicForm.exists_nhds_scalar_forall_isOrbitalIntegral_eq_mul_integral_unipotentGL2_conj_of_diagonal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/65c2b09f-cadd-5bee-84af-44423b570961
-- title:
--   Germ of split orbital integrals near a central element
-- statement:
--   Let $K$ be a number field, $v$ a finite place of $K$ with completion $F=K_v$ and valuation ring $\mathcal O_v$, and let $c\in F^{\times}$; let $\nu$ be an additive Haar measure on $F$ (for a Borel measurable structure on $F$) and let $f:\mathrm{GL}_2(F)\to\mathbb C$ be a local test function, i.e. locally constant with compact support. The assertion is that there is a neighbourhood $W$ of the central element $z=c\cdot 1\in \mathrm{GL}_2(F)$ such that for every $\gamma\in W$ whose $(0,1)$ and $(1,0)$ entries vanish and which is regular semisimple in the sense that $\operatorname{tr}(\gamma)^2-4\det(\gamma)$ is a unit of $F$, for every Haar measure $\tau$ on the centraliser $T_\gamma$ of $\{\gamma\}$ in $\mathrm{GL}_2(F)$ (with its Borel structure), and for every $I\in\mathbb C$ which is a value of the orbital integral of $f$ at $\gamma$ against $\tau$ — meaning that there is a non-negative measurable compactly supported $w$ with $\int_{T_\gamma}w(tx)\,d\tau(t)=1$ whenever $f(x^{-1}\gamma x)\neq0$, and $I=\int_{\mathrm{GL}_2(F)}f(x^{-1}\gamma x)\,w(x)\,d\mu(x)$, where $\mu$ is the Haar measure on $\mathrm{GL}_2(F)$ normalised by the compact open set $\mathrm{GL}_2(\mathcal O_v)$ of units integral together with their inverses — one has $$I=\bigl(\tau(T_\gamma\cap \mathrm{GL}_2(\mathcal O_v))\,\nu(\mathcal O_v)\,\lVert 1-\gamma_{11}/\gamma_{00}\rVert\bigr)^{-1}\int_{\mathrm{GL}_2(\mathcal O_v)}\int_F f\bigl(z\,(k^{-1}n(u)k)\bigr)\,d\nu(u)\,d\mu(k),$$ with $n(u)=\begin{pmatrix}1&u\\0&1\end{pmatrix}$ and the outer integral written using the indicator of $\mathrm{GL}_2(\mathcal O_v)$; the measures $\tau(T_\gamma\cap\mathrm{GL}_2(\mathcal O_v))$ and $\nu(\mathcal O_v)$ enter through their real values.
--
--   This is the split-torus clause of the germ expansion of orbital integrals of $\mathrm{GL}_2(F)$ about a central element: close to $z=c\cdot 1$, the orbital integral along the diagonal torus is an explicit elementary factor in $\gamma$, independent of $f$, times the $\mathrm{GL}_2(\mathcal O_v)$-averaged regular unipotent integral of $f$ at $z$, with no point term $f(z)$. It feeds the uniform germ statement near central elements used for the local comparison of trace-formula contributions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_nhds_scalar_forall_isOrbitalIntegral_eq_mul_integral_unipotentGL2_conj_of_diagonal.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain

theorem AutomorphicForm.exists_nhds_scalar_forall_isOrbitalIntegral_eq_mul_integral_unipotentGL2_conj_of_diagonal
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (c : (v.adicCompletion K)ˣ)
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (ν : Measure (v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : AutomorphicForm.IsLocalTestFn K v f) :
    ∃ W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
      ∀ γ ∈ W, (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 →
        (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 → AutomorphicForm.IsRegularSemisimple γ →
        ∀ (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ)),
          @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ →
          ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v γ τ f I →
            I = (((τ {t : AutomorphicForm.localCentralizer K v γ |
                      (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v}).toReal⁻¹ *
                  (ν (v.adicCompletionIntegers K : Set (v.adicCompletion K))).toReal⁻¹ *
                  ‖1 - (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 /
                      (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0‖⁻¹ : ℝ) : ℂ) *
              (letI := AutomorphicForm.localGLBorel K v
               ∫ k, (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ)) k *
                 (∫ u, f (Matrix.GeneralLinearGroup.scalar (Fin 2) c *
                   (k⁻¹ * AutomorphicForm.unipotentGL2 u * k)) ∂ν) ∂(AutomorphicForm.localHaar K v)) := by sorry
