-- Prove2me | Theorems.Thm_DRSOWass_Duality_lemma_4_i
-- name    : DRSOWass.Duality.lemma_4_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:28:04.040202+00:00
-- url     : https://prove2.me/theorems/fa449a68-c810-44aa-ac6e-0ac4c6e72f45
-- title:
--   Lemma 4(i) — monotonicity, upper semicontinuity and concavity of Φ(·,ζ); D̄(λ₂,ζ) ≤ D̲(λ₁,ζ) ≤ D̄(λ₁,ζ)
-- statement:
--   Let $(\Xi,d)$ be a Polish space, $p\in[1,\infty)$, $\nu$ a Borel probability measure, $\Psi\in L^1(\nu)$ Borel measurable, with $\kappa<\infty$. Then there is a $\nu$-measurable set $B$ with $\nu(B)=1$ such that:
--
--   1. for every $\zeta\in\Xi$, $\lambda\mapsto\Phi(\lambda,\zeta)$ is nondecreasing and upper semicontinuous on $\mathbb R$;
--   2. $\Phi(\lambda,\zeta)>-\infty$ for all $\lambda>\kappa$ and all $\zeta\in B$;
--   3. for $\zeta\in B$, $\Phi(\cdot,\zeta)$ is concave on $[0,\infty)$: $\Phi(t\lambda_1+(1-t)\lambda_2,\zeta)\ge t\Phi(\lambda_1,\zeta)+(1-t)\Phi(\lambda_2,\zeta)$ for $\lambda_1,\lambda_2\ge0$, $t\in(0,1)$;
--   4. for every $\varepsilon>0$, $\lambda_2>\lambda_1$ and $\zeta$ with $\Phi(\lambda_1,\zeta)>-\infty$,
--   $$\sup_{\xi\in\Xi}\{d^p(\xi,\zeta):\lambda_2d^p(\xi,\zeta)-\Psi(\xi)\le\Phi(\lambda_2,\zeta)+\varepsilon\}\le\sup_{\xi\in\Xi}\{d^p(\xi,\zeta):\lambda_1d^p(\xi,\zeta)-\Psi(\xi)\le\Phi(\lambda_1,\zeta)+\varepsilon\};$$
--   5. for $\lambda_2>\lambda_1$ and $\zeta$ with $\Phi(\lambda_1,\zeta)>-\infty$, $\overline D(\lambda_2,\zeta)\le\underline D(\lambda_1,\zeta)\le\overline D(\lambda_1,\zeta)$.
--
--   The near-optimal distance moves toward $\zeta$ as the multiplier $\lambda$ increases; this monotonicity drives the one-sided derivative bounds of Lemma 4(iii).
--
--   **Formalization Note** The paper states item 4 for every $\varepsilon\ge0$. At $\varepsilon=0$ the sets are arg mins and may be empty, and with any convention for $\sup\emptyset$ other than $+\infty$ the printed case fails (e.g. $\Xi=[0,\infty)$, $\zeta=0$, $p=1$, $\lambda_1=1$, $\lambda_2=1+\Delta$, $\Psi$ with $\xi-\Psi(\xi)=-\xi$ on $[0,1]$ and $=-1-c(1-e^{-(\xi-1)})$ beyond, $0<c<\Delta<1$: the $\lambda_1$-arg min is empty, the $\lambda_2$-arg min is $\{1\}$). The statement is therefore made for $\varepsilon>0$, the only case the paper's later proofs use. Concavity of the extended-valued $\Phi(\cdot,\zeta)$ is the explicit inequality in $[-\infty,\infty)$. $\overline D,\underline D$ are $[0,\infty]$-valued, their $\limsup$/$\liminf$ written as monotone limits. Borel measurability of $\Psi$ is added, as in p. 5.
-- source:
--   Gao, Kleywegt, Distributionally Robust Stochastic Optimization with Wasserstein Distance, arXiv:1604.02199v3, p. 10, Lemma 4(i)

import Mathlib
import Definitions.Def_DRSOWass_Duality_Setting

open MeasureTheory Filter Topology

namespace DRSOWass.Duality

/-- Lemma 4(i) (Monotonicity), p. 10, for `κ < ∞`: there is `B ∈ B_ν(Ξ)` with `ν(B) = 1` such
that `Φ(·, ζ)` is nondecreasing and upper semicontinuous for every `ζ`, finite on `(κ, ∞)`
and concave on `[0, ∞)` for `ζ ∈ B`; the sup inequality between the `ε`-optimal sets holds
for `ε > 0` (the printed `ε = 0` case is false, see the docs); and
`D̄(λ₂, ζ) ≤ D̲(λ₁, ζ) ≤ D̄(λ₁, ζ)` for `λ₁ < λ₂` with `Φ(λ₁, ζ) > −∞`. -/
theorem lemma_4_i {Ξ : Type*} [MetricSpace Ξ] [CompleteSpace Ξ] [SecondCountableTopology Ξ]
    [MeasurableSpace Ξ] [BorelSpace Ξ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν] (Ψ : Ξ → ℝ) (p : ℝ)
    (hp : 1 ≤ p) (hΨm : Measurable Ψ) (hΨ : Integrable Ψ ν)
    (hκ : growthRate Ψ ν p < ⊤) :
    ∃ B : Set Ξ, NullMeasurableSet B ν ∧ ν Bᶜ = 0 ∧
      (∀ ζ : Ξ, Monotone (fun lam : ℝ => Phi Ψ p lam ζ) ∧
        UpperSemicontinuous (fun lam : ℝ => Phi Ψ p lam ζ)) ∧
      (∀ ζ ∈ B, ∀ lam : ℝ, growthRate Ψ ν p < ENNReal.ofReal lam → ⊥ < Phi Ψ p lam ζ) ∧
      (∀ ζ ∈ B, ∀ l₁ l₂ : ℝ, 0 ≤ l₁ → 0 ≤ l₂ → ∀ t : ℝ, 0 < t → t < 1 →
        ((t : ℝ) : EReal) * Phi Ψ p l₁ ζ + ((1 - t : ℝ) : EReal) * Phi Ψ p l₂ ζ ≤
          Phi Ψ p (t * l₁ + (1 - t) * l₂) ζ) ∧
      (∀ ε : ℝ, 0 < ε → ∀ l₁ l₂ : ℝ, l₁ < l₂ → ∀ ζ : Ξ, ⊥ < Phi Ψ p l₁ ζ →
        (⨆ ξ ∈ nearOpt Ψ p l₂ ε ζ, ENNReal.ofReal (dist ξ ζ ^ p)) ≤
          ⨆ ξ ∈ nearOpt Ψ p l₁ ε ζ, ENNReal.ofReal (dist ξ ζ ^ p)) ∧
      (∀ l₁ l₂ : ℝ, l₁ < l₂ → ∀ ζ : Ξ, ⊥ < Phi Ψ p l₁ ζ →
        DUpper Ψ p l₂ ζ ≤ DLower Ψ p l₁ ζ ∧ DLower Ψ p l₁ ζ ≤ DUpper Ψ p l₁ ζ) := by sorry

end DRSOWass.Duality
