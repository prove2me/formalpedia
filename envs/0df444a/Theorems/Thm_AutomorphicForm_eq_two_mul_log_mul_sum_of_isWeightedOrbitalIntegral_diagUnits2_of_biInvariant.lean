-- Prove2me | Theorems.Thm_AutomorphicForm_eq_two_mul_log_mul_sum_of_isWeightedOrbitalIntegral_diagUnits2_of_biInvariant
-- name    : AutomorphicForm.eq_two_mul_log_mul_sum_of_isWeightedOrbitalIntegral_diagUnits2_of_biInvariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/6e218531-77e9-581b-9ff5-c6e5906707a6
-- title:
--   Weighted orbital integral at a split diagonal element as a shell sum
-- statement:
--   Let $K$ be a number field, $v$ a nonzero prime of $\mathcal O_K$, $F = K_v$ the $v$-adic completion with its normalised absolute value and $q = N(v)$ the absolute norm of the ideal $v$. Let $a,b \in F^\times$ with $a \neq b$ and put $\gamma = \mathrm{diag}(a,b) \in GL_2(F)$ (the element `diagUnits2 a b`, the diagonal matrix with entries $a,b$ and inverse $\mathrm{diag}(a^{-1},b^{-1})$). Let $\tau$ be a Haar measure, for the Borel $\sigma$-algebra, on the centraliser of $\{\gamma\}$ in $GL_2(F)$, normalised so that the set of $t$ in that centraliser whose image lies in `localIntegralSet` — the $g \in GL_2(F)$ with all entries of both $g$ and $g^{-1}$ in $\mathcal O_v$ — has measure $1$. Let $f : GL_2(F) \to \mathbb C$ be Borel measurable, bounded by a real constant $C$, and invariant under left and right multiplication by elements of `localIntegralSet`. Let $\varpi \in F$ satisfy $\|\varpi\| = q^{-1}$, and let $M \in \mathbb N$ be such that, writing $n(y)$ for the unipotent matrix $\begin{pmatrix}1&y\\0&1\end{pmatrix}$, $f(n(y)^{-1}\gamma\, n(y)) \neq 0$ forces $\|y\| \le q^{M}$. Finally let $J \in \mathbb C$ be a weighted orbital integral of $f$ at $\gamma$ for $\tau$: for some section function $s$ attached to $(\gamma,\tau,f)$ one has $J = \int_{GL_2(F)} f(x^{-1}\gamma x)\, w(x)\, s(x)\, d\mu(x)$, where $\mu$ is the Haar measure on $GL_2(F)$ giving mass $1$ to the integral points and $w(x) = 2\log\bigl(\max(\|x_{00}\|,\|x_{01}\|)\cdot \mathrm{rowMaxNorm}(x)/\|\det x\|\bigr)$. Then
--   $$J = 2\log q \sum_{s=0}^{M-1} (s+1)\bigl(q^{\,s+1}-q^{\,s}\bigr)\, f\bigl(n(\varpi^{-(s+1)})^{-1}\gamma\, n(\varpi^{-(s+1)})\bigr).$$
--
--   This is the local computation of a weighted orbital integral at a regular split diagonal element for a bi-$GL_2(\mathcal O_v)$-invariant kernel: the Iwasawa decomposition collapses the integral to a sum over the shells $\|y\| = q^{s+1}$ of unipotent parameters, with shell volume $q^{s+1}-q^{s}$ and weight $2(s+1)\log q$. It feeds the evaluation of weighted orbital integrals of base-changed Hecke operators used in the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_eq_two_mul_log_mul_sum_of_isWeightedOrbitalIntegral_diagUnits2_of_biInvariant.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.eq_two_mul_log_mul_sum_of_isWeightedOrbitalIntegral_diagUnits2_of_biInvariant
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b)
    (τ : @Measure (AutomorphicForm.localCentralizer K v (diagUnits2 a b))
      (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)) τ)
    (hτ1 : τ {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v} = 1)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfm : Measurable[AutomorphicForm.localGLBorel K v] f)
    (C : ℝ) (hfC : ∀ g, ‖f g‖ ≤ C)
    (hfK : ∀ g k₁ k₂ : GL (Fin 2) (v.adicCompletion K),
      k₁ ∈ AutomorphicForm.localIntegralSet K v → k₂ ∈ AutomorphicForm.localIntegralSet K v →
        f (k₁ * g * k₂) = f g)
    (ϖ : v.adicCompletion K) (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹) (M : ℕ)
    (hM : ∀ y : v.adicCompletion K,
      f ((AutomorphicForm.unipotentGL2 y)⁻¹ * diagUnits2 a b * AutomorphicForm.unipotentGL2 y) ≠ 0 →
        ‖y‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ M)
    (J : ℂ) (hJ : AutomorphicForm.IsWeightedOrbitalIntegral K v (diagUnits2 a b) τ f J) :
    J = ((2 * Real.log (Ideal.absNorm v.asIdeal) : ℝ) : ℂ) *
      ∑ s ∈ Finset.range M,
        ((((s + 1 : ℕ) : ℝ) * ((Ideal.absNorm v.asIdeal : ℝ) ^ (s + 1) - (Ideal.absNorm v.asIdeal : ℝ) ^ s) : ℝ) : ℂ) *
          f ((AutomorphicForm.unipotentGL2 (ϖ⁻¹ ^ (s + 1)))⁻¹ * diagUnits2 a b *
            AutomorphicForm.unipotentGL2 (ϖ⁻¹ ^ (s + 1))) := by sorry
