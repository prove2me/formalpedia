-- Prove2me | Theorems.Thm_DynStrings_claim_5_10_mgf
-- name    : DynStrings.claim_5_10_mgf
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:56:16.331107+00:00
-- url     : https://prove2.me/theorems/87568dbd-c6b2-40f1-b6e8-d6f10bfc7441
-- title:
--   Claim 5.10 — $\ln\mathbb E[e^{\nu V}]\le C_5\nu\Lambda+C_5(\Lambda/\gamma)(e^{C_5\nu\gamma}-1)$
-- statement:
--   There is an absolute constant $C_5$ such that the following holds. Let $X$ be a non-empty string and $\mathcal C$ a finite collection, both fixed independently of the random orders, and let $V$ be the total arity of the exclusive tuples whose creation round is $k+1$ for some $k\in K$. With $\Lambda=\Lambda(X\mid\mathcal C)$ and $\gamma=1+\delta(X\mid\mathcal C)$, for every $\nu\ge0$,
--
--   $$\ln\mathbb E\big[\exp(\nu V)\big]\le C_5\,\nu\,\Lambda+C_5\,\frac{\Lambda}{\gamma}\big(\exp(C_5\,\nu\,\gamma)-1\big).$$
--
--   The moment-generating function of $V$ is bounded by that of $C_5\Lambda+C_5\gamma Z$ for a Poisson variable $Z$ of mean $C_5\Lambda/\gamma$, which yields the tail of the grammar size.
--
--   Differences from the source:
--   - generalization: strings over a fixed countably infinite alphabet $\Sigma$ → strings over an arbitrary type $\alpha$ with decidable equality; reason: the statement holds for every alphabet type, and a countably infinite $\alpha$ gives the source's statement
--   - reading: X and C fixed in §5 (Theorem 5.1 assumes X non-empty) → the hypothesis `X ≠ []`; reason: standing assumption of §5, under which the statement is proved
--   - encoding: random total orders ≺_k (even k ≥ 2), paused before active, uniformly random on every fixed finite set of active symbols, independent across rounds → any probability space and `ord` with `IsRandomOrders μ ord`: each realization is a choice of the orders, each `ord k` is measurable, every list of distinct well-formed active symbols is increasing with probability 1/n!, and the rounds are independent; reason: the source's assumption written for random variables; every law satisfying the source's assumption extends to the syntactic symbol type with these properties
--   - encoding: E[exp(νV)] → integrability of exp(νV) together with the bound on the logarithm of its Bochner integral; reason: without integrability the Bochner integral would be 0 and the bound vacuous
-- source:
--   Duyster, Kociumaka, Komlós, Optimal Dynamic Strings in Compressed Space (manuscript, sha256 cfcb3de9…), Claim 5.10, p.24 (V defined in §5.4, p.23)

import Mathlib
import Definitions.Def_DynStrings_Novelty
open MeasureTheory ProbabilityTheory

namespace DynStrings

/-- **Claim 5.10** (moment-generating function), p.24.
Duyster, Kociumaka, Komlós, *Optimal Dynamic Strings in Compressed Space* (manuscript, sha256 cfcb3de9…)

There is an absolute constant `C₅` such that, for every non-empty string `X` and finite collection
`𝒞` fixed independently of the random orders, and every `ν ≥ 0`,
`ln E[exp(νV)] ≤ C₅ ν Λ + C₅ (Λ/γ)(exp(C₅ ν γ) − 1)`, where `V` is the total arity of the
exclusive tuples created in the rounds `k + 1`, `k ∈ K` (§5.4), `Λ = Λ(X | 𝒞)` and
`γ = 1 + δ(X | 𝒞)`.

**Formalization Note.** The random orders are any family satisfying `IsRandomOrders` on any
probability space. The expectation is a Bochner integral, so the statement also asserts that
`exp(νV)` is integrable. -/
theorem claim_5_10_mgf :
    ∃ C₅ : ℝ, ∀ (α : Type) [DecidableEq α] (X : List α) (𝒞 : Multiset (List α)) (Ω : Type)
      [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (ord : ℕ → Ω → StrSym α → StrSym α → Prop), X ≠ [] → IsRandomOrders μ ord →
      ∀ ν : ℝ, 0 ≤ ν →
        Integrable (fun ω => Real.exp (ν * (Vtot (fun k => ord k ω) X 𝒞 : ℝ))) μ ∧
        Real.log (∫ ω, Real.exp (ν * (Vtot (fun k => ord k ω) X 𝒞 : ℝ)) ∂μ) ≤
          C₅ * ν * Lam X 𝒞 +
            C₅ * (Lam X 𝒞 / (1 + deltaRel X 𝒞)) *
              (Real.exp (C₅ * ν * (1 + deltaRel X 𝒞)) - 1) := by sorry

end DynStrings
