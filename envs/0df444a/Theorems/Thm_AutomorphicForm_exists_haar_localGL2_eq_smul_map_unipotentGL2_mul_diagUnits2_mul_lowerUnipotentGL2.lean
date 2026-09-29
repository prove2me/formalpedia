-- Prove2me | Theorems.Thm_AutomorphicForm_exists_haar_localGL2_eq_smul_map_unipotentGL2_mul_diagUnits2_mul_lowerUnipotentGL2
-- name    : AutomorphicForm.exists_haar_localGL2_eq_smul_map_unipotentGL2_mul_diagUnits2_mul_lowerUnipotentGL2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/cf6d2732-554a-5fa1-a0a1-c45a1dbbbca9
-- title:
--   Haar measure on GL₂(Kᵥ) in big Bruhat cell coordinates
-- statement:
--   Let $K$ be a number field and $v$ a finite place of $K$, i.e. a point of the height one spectrum of $\mathcal{O}_K$, and write $F = K_v$ for the completion `v.adicCompletion K`. Both $F$ and $GL_2(F)$ carry their Borel $\sigma$-algebras (`localBorel`, `localGLBorel`, together with the fact that the latter is a Borel space for the topology). The assertion is that for every Haar measure $\mu$ on $GL_2(F)$, every Haar measure $\tau$ on $F^\times$ and every additive Haar measure $\nu$ on $F$, there exists $c \in [0,\infty]$ with $c \neq 0$ and $c \neq \infty$ such that $\mu = c \cdot \Psi_*\bigl(\rho \cdot (\nu \otimes \tau \otimes \tau \otimes \nu)\bigr)$, where the measure on $F \times F^\times \times F^\times \times F$ is the product measure weighted by the density $\rho(y,a,d,x) = \mathrm{modulus}(a d^{-1})$ — the factor by which multiplication by the nonzero scalar $a/d$ scales additive Haar measure on $F$, equal to $\lVert a/d\rVert$ by `modulus_adicCompletion_eq_nnnorm` — and where $\Psi$ sends $(y,a,d,x)$ to the product $$\begin{pmatrix}1&y\\0&1\end{pmatrix}\begin{pmatrix}d&0\\0&a\end{pmatrix}\begin{pmatrix}1&0\\x&1\end{pmatrix}$$ in $GL_2(F)$, built from `unipotentGL2`, `diagUnits2` and `lowerUnipotentGL2`.
--
--   This is the integration formula for Haar measure on $GL_2$ of a non-archimedean local field in the coordinates of the big Bruhat cell $N A N^{-}$, with the upper unipotent group on the left and the invariant density $|a/d|$; it is the companion, obtained by inversion and right invariance, of the corresponding formula with the lower unipotent group on the left. It supplies the change of variables used in the local Rankin–Selberg and Godement zeta computations, and is cited in the analysis of the local integrals attached to the long Weyl element and to Whittaker functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_haar_localGL2_eq_smul_map_unipotentGL2_mul_diagUnits2_mul_lowerUnipotentGL2.lean

import Mathlib
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

open scoped ENNReal

theorem AutomorphicForm.exists_haar_localGL2_eq_smul_map_unipotentGL2_mul_diagUnits2_mul_lowerUnipotentGL2
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    letI := localBorel K v
    letI := localGLBorel K v
    haveI := borelSpace_localGLBorel K v
    ∀ (μ : Measure (GL (Fin 2) (v.adicCompletion K))) [μ.IsHaarMeasure]
      (τ : Measure (v.adicCompletion K)ˣ) [τ.IsHaarMeasure]
      (ν : Measure (v.adicCompletion K)) [ν.IsAddHaarMeasure],
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      μ = c • Measure.map
        (fun q : v.adicCompletion K × (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ × v.adicCompletion K =>
          unipotentGL2 q.1 * diagUnits2 q.2.2.1 q.2.1 * lowerUnipotentGL2 q.2.2.2)
        ((ν.prod (τ.prod (τ.prod ν))).withDensity fun q =>
          (modulus (((q.2.1 * (q.2.2.1)⁻¹ : (v.adicCompletion K)ˣ)) : v.adicCompletion K) : ℝ≥0∞)) := by sorry
