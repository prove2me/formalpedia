-- Prove2me | Theorems.Thm_AutomorphicForm_exists_haar_localGL2_eq_smul_map_lowerUnipotentGL2_mul_diagUnits2_mul_unipotentGL2
-- name    : AutomorphicForm.exists_haar_localGL2_eq_smul_map_lowerUnipotentGL2_mul_diagUnits2_mul_unipotentGL2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/15083b11-00ce-558b-8ceb-7b686898b7ef
-- title:
--   Haar measure on GL₂(Kᵥ) in Bruhat big-cell coordinates
-- statement:
--   Let $K$ be a number field and $v$ a finite place of $K$, i.e. a point of the height-one spectrum of $\mathcal{O}_K$, and write $F = K_v$ for the $v$-adic completion. Equip $F$ with its Borel $\sigma$-algebra (`localBorel`) and $\mathrm{GL}_2(F)$ with its Borel $\sigma$-algebra (`localGLBorel`), which is a `BorelSpace` structure for the topology. The assertion is that for every Haar measure $\mu$ on the group $\mathrm{GL}_2(F)$, every Haar measure $\tau$ on the multiplicative group $F^\times$ and every additive Haar measure $\nu$ on $F$, there exists $c \in [0,\infty]$ with $c \neq 0$ and $c \neq \infty$ such that $\mu$ is $c$ times the pushforward, along the map $$(y,a,d,x) \longmapsto \begin{pmatrix}1&0\\ x&1\end{pmatrix}\begin{pmatrix}d&0\\0&a\end{pmatrix}\begin{pmatrix}1&y\\0&1\end{pmatrix}$$ from $F \times F^\times \times F^\times \times F$ to $\mathrm{GL}_2(F)$ (the three factors being `lowerUnipotentGL2 x`, `diagUnits2 d a` and `unipotentGL2 y`), of the measure $\nu \otimes \tau \otimes \tau \otimes \nu$ on the four coordinates $(y,a,d,x)$ weighted by the density $(y,a,d,x) \mapsto \mathrm{modulus}(d a^{-1})$, where $\mathrm{modulus}(u)$ is the factor by which multiplication by $u$ scales additive Haar measure on $F$ (the `distribHaarChar` of $u$, equal to $\|u\|$ for $F = K_v$).
--
--   This is the local integration formula attached to the big Bruhat cell $\mathrm{GL}_2 = B^- N \sqcup B^- w$ over a non-archimedean completion: Haar measure on $\mathrm{GL}_2(K_v)$ is, up to a positive finite constant, $|d/a|\,d\nu(x)\,d\tau(d)\,d\tau(a)\,d\nu(y)$ in the coordinates $g = n^-(x)\,\mathrm{diag}(d,a)\,n(y)$. It is used in the form with the unipotent factors interchanged and in the local Rankin–Selberg computations comparing Jacquet-type integrals with local zeta integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_haar_localGL2_eq_smul_map_lowerUnipotentGL2_mul_diagUnits2_mul_unipotentGL2.lean

import Mathlib
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal
  LanglandsTunnell.CubicInduction
open scoped ENNReal

theorem AutomorphicForm.exists_haar_localGL2_eq_smul_map_lowerUnipotentGL2_mul_diagUnits2_mul_unipotentGL2
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
          lowerUnipotentGL2 q.2.2.2 * diagUnits2 q.2.2.1 q.2.1 * unipotentGL2 q.1)
        ((ν.prod (τ.prod (τ.prod ν))).withDensity fun q =>
          (modulus (((q.2.2.1 * (q.2.1)⁻¹ : (v.adicCompletion K)ˣ)) : v.adicCompletion K) : ℝ≥0∞)) := by sorry
