-- Prove2me | Theorems.Thm_AutomorphicForm_continuous_finprod_localFactor_and_exists_fractionalIdeal_norm_finprod_le_of_isCompact
-- name    : AutomorphicForm.continuous_finprod_localFactor_and_exists_fractionalIdeal_norm_finprod_le_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/0497eea7-0d56-5ee0-8086-e28013126ad2
-- title:
--   Finite local product: continuity, fractional-ideal support, polynomial growth
-- statement:
--   Let $F$ be a number field, $S$ a finite set of height-one primes of $\mathcal O_F$, $n$ a natural number, $\mathrm{thr}$ an integer-valued function on the height-one primes, and $\Phi$ a family of functions $\Phi_{j,v}\colon F_v\times\mathbb C\to\mathbb C$ indexed by $j\in\{0,\dots,n-1\}$ and by the height-one primes $v$, where $F_v$ denotes the $v$-adic completion. Assume: $\mathrm{thr}_v=0$ for $v\notin S$; each $s\mapsto\Phi_{j,v}(w,s)$ is entire; $\Phi_{j,v}(w,s)=1$ whenever $v\notin S$ and $|w|_v=1$; $\Phi_{j,v}(w,s)=0$ whenever $w\neq0$ and $|w|_v>\exp(\mathrm{thr}_v)$; for every $R$ there are $M\ge0$ and $\kappa\in\mathbb N$ with $\|\Phi_{j,v}(w,s)\|\le M_S(v)\cdot\big(N(v)^{\max(0,-e)}\big)^{\kappa}$ for all $j,v,w,s$ with $\|s\|\le R$ and $|w|_v=\exp(e)$, where $M_S(v)=M$ for $v\in S$ and $1$ otherwise and $N(v)$ is the absolute norm of $v$; and for each $j,v$ and each $w_0\neq0$ there is $\delta\in\mathbb Z$ with $\Phi_{j,v}(w,s)=\Phi_{j,v}(w_0,s)$ whenever $|w-w_0|_v\le\exp(\delta)$, uniformly in $s$. Then two conclusions hold. First, for every idele $x_0\in\mathbb A_F^\times$ and every $j$, the map $(s,y)\mapsto\prod^{\mathrm f}_v\Phi_{j,v}\big((x_0y)_v,s\big)$, the finitely-supported product over all height-one primes of the finite-adele components of $x_0y$, is continuous on $\mathbb C\times\mathbb A_F^\times$. Second, for every compact $U\subseteq\mathbb A_F^\times$ and every real $R$ there exist $k\in\mathbb N$, a fractional ideal $I$ of $F$ and reals $c_0>0$, $c\ge0$ such that $|N_{F/\mathbb Q}(\xi)|\ge c_0$ for every nonzero $\xi\in I$, and such that for all $j$, all $s$ with $\|s\|\le R$, all $u\in U$ and all nonzero $\xi\in F$ the product $\prod^{\mathrm f}_v\Phi_{j,v}\big((\xi u)_v,s\big)$ vanishes if $\xi\notin I$ and in all cases has norm at most $c\cdot\max\big(1,|N_{F/\mathbb Q}(\xi)|\big)^{k}$.
--
--   The hypotheses axiomatise the finite local factors occurring in the explicit formula for the torus Whittaker (Fourier) coefficients of a flat Eisenstein family on $\mathrm{GL}_2$: shell conditions at the places of $S$, the value $1$ at unramified places on units, a bound on the support, a uniform polynomial bound in the valuation, and local constancy away from $0$. The two conclusions — joint continuity in the spectral parameter and the idele, and vanishing outside a fractional ideal together with polynomial growth in the norm of the frequency, uniformly on compact sets of ideles — are what the analytic continuation of the Whittaker coefficients consumes; the statement is used by [`AutomorphicForm.exists_entire_whittakerCoefficient_diagOne_continuation_of_flat_family_of_unitary`](thm.html#AutomorphicForm.exists_entire_whittakerCoefficient_diagOne_continuation_of_flat_family_of_unitary), and its proof invokes the fact that a compact subset of the finite adele ring can be scaled by a nonzero element of $\mathcal O_F$ into the integral adeles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_continuous_finprod_localFactor_and_exists_fractionalIdeal_norm_finprod_le_of_isCompact.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

open scoped Classical in

theorem AutomorphicForm.continuous_finprod_localFactor_and_exists_fractionalIdeal_norm_finprod_le_of_isCompact
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) (thr : HeightOneSpectrum (𝓞 F) → ℤ)
    (Φ : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ → ℂ)
    (_hthr : ∀ v ∉ S, thr v = 0)
    (_hΦd : ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F)) (w : v.adicCompletion F), Differentiable ℂ (Φ j v w))
    (_hΦ1 : ∀ (j : Fin n), ∀ v ∉ S, ∀ (w : v.adicCompletion F) (s : ℂ), Valued.v w = 1 → Φ j v w s = 1)
    (_hΦ0 : ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F)) (w : v.adicCompletion F) (s : ℂ), w ≠ 0 →
      WithZero.exp (thr v) < Valued.v w → Φ j v w s = 0)
    (_hΦb : ∀ R : ℝ, ∃ (M : ℝ) (κ : ℕ), 0 ≤ M ∧ ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F))
      (w : v.adicCompletion F) (e : ℤ) (s : ℂ), ‖s‖ ≤ R → Valued.v w = WithZero.exp e →
        ‖Φ j v w s‖ ≤ (if v ∈ S then M else 1) * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-e).toNat) ^ κ)
    (_hΦlc : ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F)) (w₀ : v.adicCompletion F), w₀ ≠ 0 → ∃ δ : ℤ,
      ∀ (w : v.adicCompletion F) (s : ℂ), Valued.v (w - w₀) ≤ WithZero.exp δ → Φ j v w s = Φ j v w₀ s) :
    (∀ (x₀ : (AdeleRing (𝓞 F) F)ˣ) (j : Fin n),
      Continuous fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        Φ j v (((x₀ : AdeleRing (𝓞 F) F) * (p.2 : AdeleRing (𝓞 F) F)).2 v) p.1) ∧
    (∀ (U : Set (AdeleRing (𝓞 F) F)ˣ), IsCompact U → ∀ R : ℝ,
      ∃ (k : ℕ) (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (c₀ c : ℝ), 0 < c₀ ∧ 0 ≤ c ∧
        (∀ ξ : F, ξ ∈ I → ξ ≠ 0 → c₀ ≤ ((|Algebra.norm ℚ ξ| : ℚ) : ℝ)) ∧
        ∀ (j : Fin n) (s : ℂ), ‖s‖ ≤ R → ∀ u ∈ U, ∀ ξ : F, ξ ≠ 0 →
          (ξ ∉ I → ∏ᶠ v : HeightOneSpectrum (𝓞 F),
              Φ j v ((algebraMap F (AdeleRing (𝓞 F) F) ξ * (u : AdeleRing (𝓞 F) F)).2 v) s = 0) ∧
          ‖∏ᶠ v : HeightOneSpectrum (𝓞 F),
              Φ j v ((algebraMap F (AdeleRing (𝓞 F) F) ξ * (u : AdeleRing (𝓞 F) F)).2 v) s‖
            ≤ c * (max 1 ((|Algebra.norm ℚ ξ| : ℚ) : ℝ)) ^ k) := by sorry
