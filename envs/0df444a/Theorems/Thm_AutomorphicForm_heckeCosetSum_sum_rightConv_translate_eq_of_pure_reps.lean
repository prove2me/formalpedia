-- Prove2me | Theorems.Thm_AutomorphicForm_heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps
-- name    : AutomorphicForm.heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/e8750187-b0c9-5d06-b975-59fa9175415e
-- title:
--   Sphericity and Hecke eigenvalue survive right convolution
-- statement:
--   Let $K$ be a number field, $v$ a height-one prime of $\mathcal O_K$, and $U$ a subgroup of $\mathrm{GL}_2(\mathbb A_K)$ (written $\mathrm{AdelicGL2}$) containing the image under `placeEmbed` of every $k_v\in\mathrm{GL}_2(\mathcal O_v)$, pushed forward along $\mathcal O_v\to K_v$. Let $\mathrm{reps}:\mathrm{Fin}(N(v)+1)\to\mathrm{GL}_2(\mathbb A_K)$, where $N(v)=\mathrm{absNorm}(v)$, be a Hecke coset system for $U$ and the generator `heckeGen` at $v$ — each $\mathrm{reps}\,j$ lies in $U\cdot\{\mathrm{heckeGen}\}\cdot U$, the classes $\mathrm{reps}\,j\,U$ cover that double coset, and $j\mapsto \mathrm{reps}\,j\,U$ is injective — and assume each $\mathrm{reps}\,j$ is `placeEmbed K v` of some element of $\mathrm{GL}_2(K_v)$. Let $\varphi:\mathrm{GL}_2(\mathbb A_K)\to\mathbb C$ be right $U$-invariant and a Hecke coset eigenfunction at $v$ with eigenvalue $a$, i.e. for some coset system $\mathrm{reps}'$ for $U$ and `heckeGen` one has $\sum_j\varphi(g\,\mathrm{reps}'j)=a\varphi(g)$ for all $g$. Let $f$ be such that every $z$ with $f(z)\neq0$ factors as $z=z_1z_2$ with $z_2\in U$ and $z_1$ commuting with `placeEmbed K v` of every element of $\mathrm{GL}_2(K_v)$, and such that $z\mapsto\varphi(gz)f(z)$ is integrable for the adelic Haar measure `adelicGLHaar` for each $g$. Finally let $h:\mathrm{Fin}\,n\to\mathrm{GL}_2(\mathbb A_K)$ with each $h\,i$ commuting with the same local subgroup, and $c:\mathrm{Fin}\,n\to\mathbb C$. Then $\Phi(g)=\sum_i c_i\,(\varphi *f)(g\,h_i)$, where $(\varphi*f)(g)=\int\varphi(gx)f(x)$, satisfies: $\Phi$ is invariant under right translation by `placeEmbed` of $\mathrm{GL}_2(\mathcal O_v)$; $\sum_j\Phi(g\,\mathrm{reps}\,j)=a\,\Phi(g)$ for all $g$; and consequently $\Phi$ is a Hecke coset eigenfunction at $v$ for $U$ and `heckeGen` with eigenvalue $a$. No right $U$-invariance of $\Phi$ is asserted.
--
--   This is the standard compatibility of the Hecke action at a finite place with the right regular representation, in the form needed to transport the local data at a good place (sphericity at $v$ and the eigenvalue $a$) from an automorphic form to the smoothed, right-translated test vector used in the Rankin–Selberg construction. It feeds the construction of test data for the Rankin–Selberg integral and the computation of Whittaker coefficients along powers of the Hecke generator.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps.lean

import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.SmoothCusp IsDedekindDomain UnramifiedWhittaker HeckeIntegralSeam

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (U : Subgroup (AdelicGL2 (𝓞 K) K))
    (hUv : ∀ kv : GL (Fin 2) (v.adicCompletionIntegers K),
      placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv) ∈ U)
    (reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 K) K)
    (hsys : IsHeckeCosetSystem U (heckeGen (𝓞 K) K v) reps)
    (hpure : ∀ j, ∃ m : GL (Fin 2) (v.adicCompletion K), reps j = placeEmbed K v m)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U, φ (g * u) = φ g)
    (a : ℂ) (hφT : IsHeckeCosetEigenfunctionAt K U (heckeGen (𝓞 K) K v) v φ a)
    (f : AdelicGL2 (𝓞 K) K → ℂ)
    (hsupp : ∀ z : AdelicGL2 (𝓞 K) K, f z ≠ 0 → ∃ z₁ z₂ : AdelicGL2 (𝓞 K) K,
      z = z₁ * z₂ ∧ z₂ ∈ U ∧ ∀ xv : GL (Fin 2) (v.adicCompletion K), z₁ * placeEmbed K v xv = placeEmbed K v xv * z₁)
    (hint : ∀ g : AdelicGL2 (𝓞 K) K, Integrable (fun z => φ (g * z) * f z) (adelicGLHaar (Fin 2) (𝓞 K) K))
    {n : ℕ} (h : Fin n → AdelicGL2 (𝓞 K) K) (c : Fin n → ℂ)
    (hh : ∀ i, ∀ xv : GL (Fin 2) (v.adicCompletion K), h i * placeEmbed K v xv = placeEmbed K v xv * h i) :
    let Φ : AdelicGL2 (𝓞 K) K → ℂ := fun g => ∑ i, c i * rightConv K φ f (g * h i)
    (∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
      Φ (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = Φ g) ∧
    (∀ g : AdelicGL2 (𝓞 K) K, heckeCosetSum K reps Φ g = a * Φ g) ∧
    IsHeckeCosetEigenfunctionAt K U (heckeGen (𝓞 K) K v) v Φ a := by sorry
