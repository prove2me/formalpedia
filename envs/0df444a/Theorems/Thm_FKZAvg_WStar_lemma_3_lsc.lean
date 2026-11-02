-- Prove2me | Theorems.Thm_FKZAvg_WStar_lemma_3_lsc
-- name    : FKZAvg.WStar.lemma_3_lsc
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-01T15:15:55.537195+00:00
-- url     : https://prove2.me/theorems/29de08b7-a13b-40ac-b5c0-6a83216dc886
-- title:
--   Lemma 3 (corrected) — u* of (15) is lower semicontinuous and attained by some f ∈ 𝔽; A_*(x) has Borel graph and compact values
-- statement:
--   Lemma 3 of Feinberg–Kasyanov–Zadoianchuk (2012), with the claim $u^*\in L(\mathbb X)$ weakened to what the printed proof establishes: lower semicontinuity of $u^*$.
--
--   Setting: the model `SchalAvg.AvgOpt.Model` (separable metrizable standard Borel spaces $\mathbb X,\mathbb A$, nonempty action sets $A(x)$ with Borel graph, $[0,+\infty]$-valued cost $c$, transition probability $q$), with a measurable selector of $A$ (standing assumption (ii) of §2). $L(\mathbb X)$ is the class of lower semicontinuous $u:\mathbb X\to[0,+\infty]$ with $\{x:u(x)<+\infty\}\neq\emptyset$; $\mathbb F$ is the set of stationary policies (measurable $f$ with $f(x)\in A(x)$).
--
--   **Lemma 3 (corrected).** If Assumption $(\mathrm W^*)$ holds and $u\in L(\mathbb X)$, then the function
--   $$u^*(x):=\inf_{a\in A(x)}\Big[c(x,a)+\int_{\mathbb X}u(y)\,q(dy\mid x,a)\Big],\qquad x\in\mathbb X,\tag{15}$$
--   is lower semicontinuous, and there exists $f\in\mathbb F$ with
--   $$u^*(x)=c(x,f(x))+\int_{\mathbb X}u(y)\,q(dy\mid x,f(x)),\qquad x\in\mathbb X.\tag{16}$$
--   Moreover the infimum in (15) is a minimum, and the nonempty sets
--   $$A_*(x)=\Big\{a\in A(x):u^*(x)=c(x,a)+\int_{\mathbb X}u(y)\,q(dy\mid x,a)\Big\}\tag{17}$$
--   satisfy: (a) $\mathrm{Gr}(A_*)$ is a Borel subset of $\mathbb X\times\mathbb A$; (b) if $u^*(x)=+\infty$ then $A_*(x)=A(x)$, and if $u^*(x)<+\infty$ then $A_*(x)$ is compact.
--
--   The printed Lemma 3 claims $u^*\in L(\mathbb X)$, which also requires $\mathrm{dom}\,u^*\neq\emptyset$; that can fail (see the disproof of `FKZAvg.WStar.lemma_3`). The proof only shows lower semicontinuity, which is all later uses need. The existence of $f$ uses the Arsenin–Kunugui uniformization theorem applied to $\mathrm{Gr}(A_*)$ over $\{u^*<\infty\}$ (the printed proof writes $\mathrm{Gr}(A)$ there, a misprint).
-- source:
--   Feinberg, Kasyanov & Zadoianchuk, Average Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, Math. Oper. Res. 37(4) 2012, pp. 597-598, Lemma 3 (u* lower semicontinuous instead of u* in L(X), as established by its proof)

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model
import Definitions.Def_FKZAvg_WStar_Assumptions

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter SchalAvg.AvgOpt

namespace FKZAvg.WStar

/-- Lemma 3 (p. 597), corrected: `u*` is lower semicontinuous (its domain may be empty). -/
theorem lemma_3_lsc {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (M : Model X A) (hsel : HasSelector M)
    (hW : CondWStar M) (u : X → ℝ≥0∞) (hu : InL u) :
    LowerSemicontinuous (uStar M u) ∧
    (∃ f : X → A, IsStationary M f ∧ ∀ x, uStar M u x = eta M u 1 x (f x)) ∧
    (∀ x, (AsubStar M u x).Nonempty) ∧
    MeasurableSet {p : X × A | p.2 ∈ AsubStar M u p.1} ∧
    ∀ x, (uStar M u x = ⊤ → AsubStar M u x = M.Aset x) ∧
      (uStar M u x ≠ ⊤ → IsCompact (AsubStar M u x)) := by sorry

end FKZAvg.WStar
