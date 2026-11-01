-- Prove2me | Theorems.Thm_BernoulliPoA_lemma_1
-- name    : BernoulliPoA.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:42:48.575497+00:00
-- url     : https://prove2.me/theorems/9a171281-8a72-4745-856e-92833c3a5c1f
-- title:
--   Lemma 1, p.14 — binomial thinning
-- statement:
--   Let $Y_1,\dots,Y_m$ and $Z_1,\dots,Z_m$ be independent random variables with $Y_i\sim\mathrm{Bernoulli}(r_i)$ and $Z_i\sim\mathrm{Bernoulli}(q)$, and let $Y=\sum_{i=1}^mY_i$, $X=\sum_{i=1}^mY_iZ_i$. For a cost function $c$,
--   $$
--   q\,\mathsf E[c(1+X)]=\mathsf E[c^q(1+Y)],\qquad\mathsf E[X\,c(X)]=\mathsf E[Y\,c^q(Y)].
--   $$
--   In particular, if $X\sim\mathrm{Binomial}(m,q)$, then
--   $$
--   q\,\mathsf E[c(1+X)]=c^q(1+m),\qquad\mathsf E[X\,c(X)]=m\,c^q(m).
--   $$
--
--   These identities are what turn participation probabilities below $q$ into costs $c^q$.
--
--   **Formalization Note** All variables live on one probability space and take values in $\{0,1\}$; the binomial law is given by its point masses. Every integrand is bounded on an event of full probability, so it is integrable.
--
--   Differences from the source:
--   - reading: two families of independent random variables → the whole family (Y_1,…,Y_m,Z_1,…,Z_m) is jointly independent; reason: the proof conditions on Y and needs X | Y = k ∼ Binomial(k,q); independence within each family alone would not give it
--   - generalization: c : ℕ → ℝ₊ → c : ℕ → ℝ arbitrary; reason: the identities are linear in c, and nonnegative costs are instances
--   - encoding: Yi ∼ Bernoulli(ri), Zi ∼ Bernoulli(q), X ∼ Binomial(m,q) → measurable ℕ-valued functions with values in {0,1} and P(Yi = 1) = ri, P(Zi = 1) = q; the binomial law of X given by its point masses P(X = j) = C(m,j) q^j (1−q)^(m−j); reason: Lean convention for random variables with these laws; same instances
-- source:
--   Cominetti et al., Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games, arXiv:1903.03309v8, Lemma 1, p.14

import Mathlib
import Definitions.Def_BernoulliPoA_binomExp
open MeasureTheory
open ProbabilityTheory

namespace BernoulliPoA

/-- **Lemma 1 (binomial thinning).** Cominetti et al., *Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games*, arXiv:1903.03309v8, Lemma 1, p.14: with `Y = ∑_{i=1}^m Y_i`, `X = ∑_{i=1}^m Y_i Z_i`, `Y_i ∼ Bernoulli(r_i)`, `Z_i ∼ Bernoulli(q)`
independent, `q E[c(1 + X)] = E[c^q(1 + Y)]` and `E[X c(X)] = E[Y c^q(Y)]`; and if `X ∼ Binomial(m, q)` then
`q E[c(1 + X)] = c^q(1 + m)` and `E[X c(X)] = m c^q(m)`.

**Formalization Note** The variables are `ℕ`-valued with values in `{0, 1}`, and the whole family `(Y_1, …, Y_m, Z_1, …, Z_m)` is independent
(`iIndepFun` over `Fin m ⊕ Fin m`), the reading under which the lemma's proof conditions on `Y`. In the last clause the binomial law is stated by its
point masses. All integrands take finitely many values a.s., so they are `Integrable` automatically and no integral below is a junk value.
The cost `c` is an arbitrary real function, as the identities are linear in `c`. -/
theorem lemma_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : ℕ) (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) (c : ℕ → ℝ) :
    (∀ (r : Fin m → ℝ) (Y Z : Fin m → Ω → ℕ), (∀ i, 0 ≤ r i ∧ r i ≤ 1) →
      (∀ i, Measurable (Y i)) → (∀ i, Measurable (Z i)) →
      (∀ i ω, Y i ω = 0 ∨ Y i ω = 1) → (∀ i ω, Z i ω = 0 ∨ Z i ω = 1) →
      (∀ i, P.real {ω | Y i ω = 1} = r i) → (∀ i, P.real {ω | Z i ω = 1} = q) →
      iIndepFun (Sum.elim Y Z) P →
      (q * ∫ ω, c (1 + ∑ i, Y i ω * Z i ω) ∂P = ∫ ω, binomExp c q (1 + ∑ i, Y i ω) ∂P) ∧
      (∫ ω, ((∑ i, Y i ω * Z i ω : ℕ) : ℝ) * c (∑ i, Y i ω * Z i ω) ∂P =
        ∫ ω, ((∑ i, Y i ω : ℕ) : ℝ) * binomExp c q (∑ i, Y i ω) ∂P)) ∧
    (∀ X : Ω → ℕ, Measurable X →
      (∀ j : ℕ, P.real {ω | X ω = j} = (m.choose j : ℝ) * q ^ j * (1 - q) ^ (m - j)) →
      (q * ∫ ω, c (1 + X ω) ∂P = binomExp c q (1 + m)) ∧
      (∫ ω, (X ω : ℝ) * c (X ω) ∂P = (m : ℝ) * binomExp c q m)) := by sorry

end BernoulliPoA
