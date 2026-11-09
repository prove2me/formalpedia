-- Prove2me | Theorems.Thm_BarelyTestable_LowerBound_yao
-- name    : BarelyTestable.LowerBound.yao
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:22:23.315402+00:00
-- url     : https://prove2.me/theorems/721cd0c5-8f43-4378-bf5c-f30dfb052824
-- title:
--   Claim A.1 — Yao acceptance-gap principle for arbitrary properties
-- statement:
--   Let $P$ be any property of real functions on the $n$-cube, let $0<\varepsilon,\eta<1$, and let $q$ be a natural query budget. Let $D_+$ and $D_-$ be arbitrary function distributions, with every YES function in $P$ and a NO function $\varepsilon$-far with probability at least $1-\eta$. Suppose every deterministic adaptive procedure with budget $q$, whose acceptance events under these laws are measurable, satisfies
--
--   $$\big|\Pr_{D_+}[A(F)=1]-\Pr_{D_-}[A(F)=1]\big|<1/3-\eta.$$
--
--   Then every randomized $\varepsilon$-tester correct at this dimension has worst-case query cost strictly greater than $q$, expressed by failure of the budget-$q$ predicate. Both the strict gap and strict conclusion are preserved. Distributions and seed spaces need not have finite or countable support.
--
--   Differences from the source:
--   - encoding: Boolean vectors with coordinates numbered from 1 → finite subsets of Fin n, numbered from 0; reason: the incidence-vector bijection preserves every vertex, union, intersection and coordinate square
--   - encoding: general function distributions → arbitrary probability spaces XiYes and XiNo with function-valued samples; reason: any law is represented by the identity sample on its own probability space; no finite-support restriction is made
--   - encoding: probabilities of evaluations, runs and farness, with independent tester coins → measurable coordinate evaluations, farness and deterministic acceptance events, plus measurable joint acceptance events on each seed/input product; reason: these are the events used in the source averaging proof; product probabilities give the stated independence, and measurability excludes only undefined probability expressions
--   - encoding: every ε-tester makes more than q queries at dimension n → every tester correct at n fails TesterBudget q; reason: only fixed-dimension correctness is used by the source proof; a family correct eventually specializes at every dimension beyond its correctness threshold
-- source:
--   Diptaksho Palit, Yuichi Yoshida, STOC 2027 submission #722 (October 2026), Claim A.1, p. 30 (printed = PDF page); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/722.pdf; PDF SHA256 a095e6ef801edf5b0ce3967efca977e04b7a0b4374e874116509d73837bd14f3

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Protocol

set_option autoImplicit false

namespace BarelyTestable.LowerBound

open NonmonotoneSubmod.Shared MeasureTheory

/-- Claim A.1, p.30. General input laws; all probability events and the two joint
randomized-run events are measurable. No finite-support law or finite-seed restriction. -/
theorem yao {n : ℕ} (P : Oracle (Fin n) → Prop) (ε η : ℝ)
    (hε : 0 < ε ∧ ε < 1) (hη : 0 < η ∧ η < 1) (q : ℕ)
    {XiYes XiNo : Type} [MeasurableSpace XiYes] [MeasurableSpace XiNo]
    (Dyes : Measure XiYes) (Dno : Measure XiNo) [IsProbabilityMeasure Dyes] [IsProbabilityMeasure Dno]
    (Fyes : XiYes → Oracle (Fin n)) (Fno : XiNo → Oracle (Fin n))
    (hEvalYes : ∀ x, Measurable (fun ξ => Fyes ξ x))
    (hEvalNo : ∀ x, Measurable (fun ξ => Fno ξ x))
    (hyes : ∀ ξ, P (Fyes ξ))
    (hfar_meas : MeasurableSet {ξ | Far P ε (Fno ξ)})
    (hno : 1 - η ≤ Dno.real {ξ | Far P ε (Fno ξ)})
    (hgap : ∀ A : Procedure (Fin n), Budget A q →
      MeasurableSet {ξ | Accepts A (Fyes ξ)} → MeasurableSet {ξ | Accepts A (Fno ξ)} →
        |Dyes.real {ξ | Accepts A (Fyes ξ)} - Dno.real {ξ | Accepts A (Fno ξ)}| < 1/3 - η)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Tester (Fin n) Ω)
    (hjointYes : MeasurableSet {p : Ω × XiYes | Accepts (T.procedure p.1) (Fyes p.2)})
    (hjointNo : MeasurableSet {p : Ω × XiNo | Accepts (T.procedure p.1) (Fno p.2)})
    (hcorrect : Correct μ T P ε) :
    ¬TesterBudget T q := by sorry

end BarelyTestable.LowerBound
