-- Prove2me | Theorems.Thm_DDROFB_theorem_3a
-- name    : DDROFB.theorem_3a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:07:29.022117+00:00
-- url     : https://prove2.me/theorems/67e6528e-080f-4ba0-ac62-c6eeb71188f7
-- title:
--   Theorem 3(a): the schema's family simultaneously implies a guarantee with probability at least $1-\alpha$
-- statement:
--   Let $\mathbb P^*$ be a probability measure on $\mathbb R^d$ and let $\mathcal S = (\hat u^1,\dots,\hat u^N)$ be $N$ i.i.d. draws from $\mathbb P^*$, with law $\mathbb P^*_{\mathcal S}$. Let $\alpha \in \mathbb R$. Suppose that to every sample $\mathcal S$ are attached a set of measures $\mathcal P(\mathcal S)$, not depending on $\epsilon$, and a family of sets $\{\mathcal U(\mathcal S, \epsilon) : 0<\epsilon<1\}$ in $\mathbb R^d$ such that
--
--   1. (confidence region at level $\alpha$) $\ \mathbb P^*_{\mathcal S}\bigl(\mathbb P^* \in \mathcal P(\mathcal S)\bigr) \ge 1-\alpha$;
--   2. (Steps 2–3 of the schema) $\ \mathrm{VaR}^{\mathbb P}_\epsilon(v) \le \delta^*(v \mid \mathcal U(\mathcal S,\epsilon))$ for every $\mathcal S$, every $\mathbb P \in \mathcal P(\mathcal S)$, every $0<\epsilon<1$ and every $v$;
--   3. every $\mathcal U(\mathcal S,\epsilon)$, $0<\epsilon<1$, is nonempty, convex and compact.
--
--   Then
--
--   $$
--   \mathbb P^*_{\mathcal S}\bigl(\{\mathcal U(\mathcal S,\epsilon) : 0<\epsilon<1\} \text{ simultaneously implies a probabilistic guarantee for } \mathbb P^*\bigr) \;\ge\; 1-\alpha .
--   $$
--
--   When the confidence region does not depend on $\epsilon$, a single event of probability $1-\alpha$ secures the guarantee at every level at once, so the level may be chosen after seeing the data.
--
--   Differences from the source:
--   - reading: P(S,α) the ϵ-independent confidence region of a hypothesis test at level α → an arbitrary set Pset S of measures with P∗_S(P∗ ∈ Pset S) ≥ 1 − α (hcov); reason: this coverage property is the paper's description of a confidence region (p. 9) and is the only property the proof uses (p. ec2)
--   - reading: U(S,ϵ,α) the closed convex set with δ∗(·|U) = g for a real-valued g → U S ε nonempty, convex and compact for 0 < ε < 1; reason: a closed convex set whose support function is finite everywhere is nonempty and bounded
--   - encoding: Step 2 bound with g convex, positively homogeneous, and Step 3 g = δ∗(·|U), for each 0 < ϵ < 1 → hstep2: VaR P ε v ≤ supportFn (U S ε) v for every P ∈ Pset S, 0 < ε < 1 and v; reason: substituting g = δ∗(·|U); convexity and positive homogeneity hold for every support function
--   - generalization: 0 < α < 1 → any real α; reason: the statement for every α contains the paper's case
--   - encoding: probability with respect to the sampling → product measure Measure.pi of N copies of P∗ on samples S : Fin N → ℝ^d, applied to the event as an outer measure; reason: for a measurable event this is its probability; the paper does not discuss measurability of the event
-- source:
--   Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Theorem 3(a), pp. 11–12 (proof pp. ec1–ec2)

import Mathlib
import Definitions.Def_DDROFB_supportFn
import Definitions.Def_DDROFB_VaR
import Definitions.Def_DDROFB_SimultaneouslyImplies
open MeasureTheory

namespace DDROFB

/-- **Theorem 3(a): the schema's family simultaneously implies a guarantee with probability
`1 − α`.**
Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Theorem 3(a),
pp. 11–12: "Suppose `P(S,α,ϵ) ≡ P(S,α)` does not depend on `ϵ` in Step 1 above. Let
`{U(S,ϵ,α) : 0 < ϵ < 1}` be the resulting family of sets obtained from the our schema. a) With
probability at least `1 − α` with respect to the sampling, `{U(S,ϵ,α) : 0 < ϵ < 1}` simultaneously
implies a probabilistic guarantee for `P∗`." (Proof on pp. ec1–ec2.)

**Formalization Note.** The sample is `S : Fin N → ℝ^d`, drawn from the product measure
`Measure.pi (fun _ => Pstar)` (p. 6: "the N-fold product distribution of P∗"). The `ε`-free
confidence region `Pset S` enters through the coverage hypothesis `hcov` (p. 9: a confidence
region contains `P∗` with probability at least `1 − α`). Steps 2–3 of the schema (p. 10) for every
`0 < ε < 1`, with `g = δ∗(·| U S ε)` substituted, give `hstep2`; each `U S ε` is nonempty, convex
and compact (a closed convex set with a real-valued support function). Values of the family
outside `0 < ε < 1` are never read. Probabilities of events of samples are the product (outer)
measure of the event. The schema's `0 < α < 1` is not needed. -/
theorem theorem_3a {d N : ℕ} (Pstar : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure Pstar] (α : ℝ)
    (Pset : (Fin N → EuclideanSpace ℝ (Fin d)) → Set (Measure (EuclideanSpace ℝ (Fin d))))
    (U : (Fin N → EuclideanSpace ℝ (Fin d)) → ℝ → Set (EuclideanSpace ℝ (Fin d)))
    (hU : ∀ S, ∀ ε : ℝ, 0 < ε → ε < 1 →
      (U S ε).Nonempty ∧ Convex ℝ (U S ε) ∧ IsCompact (U S ε))
    (hstep2 : ∀ S, ∀ P ∈ Pset S, ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ v, VaR P ε v ≤ supportFn (U S ε) v)
    (hcov : 1 - α ≤ (Measure.pi (fun _ : Fin N => Pstar) {S | Pstar ∈ Pset S}).toReal) :
    1 - α ≤ (Measure.pi (fun _ : Fin N => Pstar)
      {S | SimultaneouslyImplies (U S) Pstar}).toReal := by sorry

end DDROFB
