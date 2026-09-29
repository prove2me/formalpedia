-- Prove2me | Theorems.Thm_AutomorphicForm_exists_lintegral_ite_bottomRow_maximalCompactHaar_eq_mul_lintegral_maximalCompactAtHaar_empty
-- name    : AutomorphicForm.exists_lintegral_ite_bottomRow_maximalCompactHaar_eq_mul_lintegral_maximalCompactAtHaar_empty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/c1968e91-3f19-5288-8ac4-faf1fc1ece66
-- title:
--   Averaging a bottom-row valuation condition over the adelic maximal compact
-- statement:
--   Let $K$ be a number field, $S$ a finite set of nonzero primes of $\mathcal O_K$ and $n$ a natural number. Write $\mathbf K =$ `adelicMaximalCompact K` for the subgroup of $GL_2(\mathbb A_K)$ consisting of those $k$ whose finite part `glFin` lies in `finiteIntegralGL2`, i.e. in `finiteLevelZero (𝓞 K) K ⊤`, and whose archimedean component at each infinite place $w$ is a row isometry in the sense of `IsRowIsometry` (its determinant has norm $1$ and $\|xk_{00}+yk_{10}\|^2+\|xk_{01}+yk_{11}\|^2=\|x\|^2+\|y\|^2$ for all scalars $x,y$ in $w$'s completion); write $\mathbf K_\varnothing$ for `maximalCompactAt K ∅`, the intersection of $\mathbf K$ with the kernels of the local components `finComponent v ∘ glFin` at every finite place $v$. Both carry the Haar measures `maximalCompactHaar K` and `maximalCompactAtHaar K ∅` attached to their top subgroups. The assertion is that there is a real $\kappa>0$, depending only on $K$, $S$ and $n$, with the following two properties. First, for every measurable $F\colon GL_2(\mathbb A_K)\to[0,\infty]$ satisfying $F(kk')=F(k)$ whenever $\mathrm{glArch}(k')=1$, the lower integral over $\mathbf K$ of the function equal to $F(k)$ when $v(k_{10})\le v(k_{11})\cdot q_v^{-n}$ (in the value group $\mathbb Z^{\mathrm{mult}}$ with zero, the shift being `Multiplicative.ofAdd (-n)`) for all $v\in S$, and $0$ otherwise, equals $\kappa$ times the lower integral of $F$ over $\mathbf K_\varnothing$. Second, the same identity of Bochner integrals holds, with $\kappa$ read in $\mathbb C$, for every $F\colon GL_2(\mathbb A_K)\to\mathbb C$ whose restrictions to $\mathbf K$ and to $\mathbf K_\varnothing$ are almost everywhere strongly measurable for the respective measures, which is bounded in norm by some real $B$, and which satisfies the same invariance $F(kk')=F(k)$ for $\mathrm{glArch}(k')=1$. Here the entries $k_{10},k_{11}$ are the second-row entries of the matrix underlying $k$, and $v$ is applied to the finite-adelic part of these adeles at the place $v$.
--
--   This is the statement that integrating a function of the archimedean variable alone against the characteristic function of a bottom-row congruence condition at the places of $S$ over the maximal compact subgroup of $GL_2(\mathbb A_K)$ reproduces, up to a positive constant of proportionality (classically the reciprocal index of the local subgroups $K^0(\mathfrak p_v^n)$), the integral over the archimedean factor. It is used in the Rankin–Selberg part of the argument, by [`AutomorphicForm.RankinSelberg.exists_integral_torus_pair_eq_mul_integral_archTorus_of_ball_surgery`](thm.html#AutomorphicForm.RankinSelberg.exists_integral_torus_pair_eq_mul_integral_archTorus_of_ball_surgery).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_lintegral_ite_bottomRow_maximalCompactHaar_eq_mul_lintegral_maximalCompactAtHaar_empty.lean

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm IsDedekindDomain
open scoped ENNReal NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.exists_lintegral_ite_bottomRow_maximalCompactHaar_eq_mul_lintegral_maximalCompactAtHaar_empty
    (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧
      (∀ F : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable F →
        (∀ k k' : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K k' = 1 → F (k * k') = F k) →
        (∫⁻ k, (if (∀ v ∈ S, Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
              Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then F k else 0) ∂(maximalCompactHaar K)) =
          ENNReal.ofReal κ * ∫⁻ k, F k ∂(maximalCompactAtHaar K ∅)) ∧
      (∀ F : AdelicGL2 (𝓞 K) K → ℂ,
        AEStronglyMeasurable (fun k : ↥(adelicMaximalCompact K) => F k) (maximalCompactHaar K) →
        AEStronglyMeasurable (fun k : ↥(maximalCompactAt K ∅) => F k) (maximalCompactAtHaar K ∅) →
        (∃ B : ℝ, ∀ k, ‖F k‖ ≤ B) →
        (∀ k k' : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K k' = 1 → F (k * k') = F k) →
        (∫ k, (if (∀ v ∈ S, Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
              Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then F k else 0) ∂(maximalCompactHaar K)) =
          (κ : ℂ) * ∫ k, F k ∂(maximalCompactAtHaar K ∅)) := by sorry
