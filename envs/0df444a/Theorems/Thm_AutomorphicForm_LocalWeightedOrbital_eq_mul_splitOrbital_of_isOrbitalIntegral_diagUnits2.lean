-- Prove2me | Theorems.Thm_AutomorphicForm_LocalWeightedOrbital_eq_mul_splitOrbital_of_isOrbitalIntegral_diagUnits2
-- name    : AutomorphicForm.LocalWeightedOrbital.eq_mul_splitOrbital_of_isOrbitalIntegral_diagUnits2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/7352ad04-f769-593f-b77f-dc8fba69dddc
-- title:
--   Split orbital integral at diag(a,b) in Iwasawa form
-- statement:
--   Let $K$ be a number field, $v$ a finite place of $K$ (a height-one prime of $\mathcal O_K$), and let $a,b$ be units of the completion $K_v$ with $a \neq b$; put $\gamma = \mathrm{diag}(a,b) =$ `diagUnits2 a b` in $GL_2(K_v)$. Let $\tau$ be a Haar measure on the centraliser of $\{\gamma\}$ in $GL_2(K_v)$, taken with its Borel $\sigma$-algebra, let $\nu$ be an additive Haar measure on $K_v$ for a Borel measurable structure on $K_v$, and let $f : GL_2(K_v) \to \mathbb{C}$ be locally constant with compact support. Suppose $I \in \mathbb{C}$ is an orbital integral of $f$ at $\gamma$ relative to $\tau$, i.e. there is a non-negative measurable compactly supported $w$ on $GL_2(K_v)$ with $\int_{T} w(tx)\,d\tau(t) = 1$ for every $x$ with $f(x^{-1}\gamma x) \neq 0$, and $I = \int f(x^{-1}\gamma x)\,w(x)\,d\mu(x)$ for the Haar measure `localHaar` on $GL_2(K_v)$ normalised by the set $S$ of $g \in GL_2(K_v)$ with both $g$ and $g^{-1}$ having entries in $\mathcal O_v$. Then $$I = \bigl(\tau\{t \in T : t \in S\}\cdot \nu(\mathcal O_v)\cdot \|1 - b a^{-1}\|\bigr)^{-1}\, \cdot \;\mathrm{splitOrbital},$$ the three real factors being inverted separately after passing to real values, and $\mathrm{splitOrbital}$ being $\int_{K_v} \bigl(\int f(\mathrm{arg}\,k\,a\,b\,x)\,d(\mu|_S)(k)\bigr) d\nu(x)$, where `arg` is the group element attached by the project to $k$, $a$, $b$ and $x$.
--
--   This is the evaluation of the local orbital integral at a split regular element $\mathrm{diag}(a,b)$ of $GL_2(K_v)$ in Iwasawa coordinates, with the unipotent variable as the outer integration variable and the compact variable inner, in the normalisation used by the weighted orbital integral formalism. It feeds the comparison of ordinary and twisted local orbital integrals for matching split elements, [`AutomorphicForm.ratio_mul_eq_splitOrbital_of_isTwistedOrbitalIntegral_of_normString_diagUnits2_eq_of_areMatchingLocal`](thm.html#AutomorphicForm.ratio_mul_eq_splitOrbital_of_isTwistedOrbitalIntegral_of_normString_diagUnits2_eq_of_areMatchingLocal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_LocalWeightedOrbital_eq_mul_splitOrbital_of_isOrbitalIntegral_diagUnits2.lean

import Definitions.Def_AutomorphicForm_LocalWeightedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.LocalWeightedOrbital.eq_mul_splitOrbital_of_isOrbitalIntegral_diagUnits2
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b)
    (τ : @Measure (AutomorphicForm.localCentralizer K v (diagUnits2 a b))
      (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)) τ)
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (ν : Measure (v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : AutomorphicForm.IsLocalTestFn K v f)
    (I : ℂ) (hI : AutomorphicForm.IsOrbitalIntegral K v (diagUnits2 a b) τ f I) :
    letI := AutomorphicForm.localGLBorel K v
    I = (((τ {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v}).toReal⁻¹ *
          (ν (v.adicCompletionIntegers K : Set (v.adicCompletion K))).toReal⁻¹ *
          (AutomorphicForm.LocalWeightedOrbital.ratio (fun x : v.adicCompletion K => ‖x‖) a b)⁻¹ : ℝ) : ℂ) *
      AutomorphicForm.LocalWeightedOrbital.splitOrbital
        ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) ν f a b := by sorry
