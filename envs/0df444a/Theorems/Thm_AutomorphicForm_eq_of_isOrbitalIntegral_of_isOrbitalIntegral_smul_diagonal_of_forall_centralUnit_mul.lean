-- Prove2me | Theorems.Thm_AutomorphicForm_eq_of_isOrbitalIntegral_of_isOrbitalIntegral_smul_diagonal_of_forall_centralUnit_mul
-- name    : AutomorphicForm.eq_of_isOrbitalIntegral_of_isOrbitalIntegral_smul_diagonal_of_forall_centralUnit_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/9067dd5f-076a-540a-ae3c-9240f362865e
-- title:
--   Local orbital integrals agree under central-unit translation of a diagonal class
-- statement:
--   Let $K$ be a number field, $v$ a nonzero prime of $\mathcal{O}_K$, and work in $GL_2$ over the completion $K_v$. Let $g,g'\in GL_2(K_v)$, with $g$ regular semisimple in the sense that $\operatorname{tr}(g)^2-4\det(g)$ is a unit of $K_v$, and with $g$ diagonal (its $(0,1)$ and $(1,0)$ entries vanish). Suppose $g'=\varepsilon g$ as matrices for some $\varepsilon\in K_v$ with $\mathrm{v}(\varepsilon)=1$. Let $\tau$ and $\tau'$ be Haar measures for the Borel $\sigma$-algebras on the centralisers of $\{g\}$ and of $\{g'\}$ in $GL_2(K_v)$, each normalised so that the preimage under the inclusion of the set [`AutomorphicForm.localIntegralSet`](def/AutomorphicForm_LocalOrbitalBase.html#L100) of those $x\in GL_2(K_v)$ with both $x$ and $x^{-1}$ having all entries in the valuation ring of $K_v$ has mass $1$. Let $f\colon GL_2(K_v)\to\mathbb{C}$ be locally constant with compact support, and assume $f(cy)=f(y)$ for all $y$ and every $c\in GL_2(K_v)$ whose matrix is $\varepsilon'\cdot 1$ for some $\varepsilon'$ with $\mathrm{v}(\varepsilon')=1$. Finally let $I,I'\in\mathbb{C}$ be orbital integrals of $f$ at $g$ with respect to $\tau$, respectively at $g'$ with respect to $\tau'$: that is, there is a nonnegative measurable compactly supported weight $w$ on $GL_2(K_v)$ with $\int_{Z} w(tx)\,\mathrm{d}\tau(t)=1$ whenever $f(x^{-1}gx)\neq 0$ (the integral over the centralizer $Z$), and $I=\int f(x^{-1}gx)\,w(x)\,\mathrm{d}\,$`localHaar`$(x)$, and likewise for $I'$, $g'$, $\tau'$. Then $I'=I$.
--
--   This is the invariance of local orbital integrals at a split regular semisimple class under multiplication of the class by a central unit scalar, together with independence of the choice of unit-normalised Haar measure on the centralising torus and of the section function used to define the orbital integral. It serves to transport local orbital integrals at the places of a Hecke word from a class $\operatorname{diag}(zu,z)$ to a normalised representative, and is used in the global computations of integrals of orbital terms against central data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_eq_of_isOrbitalIntegral_of_isOrbitalIntegral_smul_diagonal_of_forall_centralUnit_mul.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem AutomorphicForm.eq_of_isOrbitalIntegral_of_isOrbitalIntegral_smul_diagonal_of_forall_centralUnit_mul
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (g g' : GL (Fin 2) (v.adicCompletion K)) (hg : AutomorphicForm.IsRegularSemisimple g)
    (hg₀₁ : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0)
    (hg₁₀ : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0)
    (ε : v.adicCompletion K) (hε : Valued.v ε = 1)
    (hg' : (g' : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      ε • (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (τ : @Measure (AutomorphicForm.localCentralizer K v g) (AutomorphicForm.localCentralizerBorel K v g))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v g) τ)
    (hτ1 : τ (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (τ' : @Measure (AutomorphicForm.localCentralizer K v g') (AutomorphicForm.localCentralizerBorel K v g'))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v g') τ')
    (hτ'1 : τ' (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : AutomorphicForm.IsLocalTestFn K v f)
    (hcen : ∀ c : GL (Fin 2) (v.adicCompletion K),
      (∃ ε : v.adicCompletion K, Valued.v ε = 1 ∧
        (c : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = ε • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) →
      ∀ y : GL (Fin 2) (v.adicCompletion K), f (c * y) = f y)
    (I I' : ℂ) (hI : AutomorphicForm.IsOrbitalIntegral K v g τ f I)
    (hI' : AutomorphicForm.IsOrbitalIntegral K v g' τ' f I') :
    I' = I := by sorry
