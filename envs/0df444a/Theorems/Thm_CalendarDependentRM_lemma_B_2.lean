-- Prove2me | Theorems.Thm_CalendarDependentRM_lemma_B_2
-- name    : CalendarDependentRM.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:53.047848+00:00
-- url     : https://prove2.me/theorems/b755b7dc-5368-487a-a097-2f0ccac3b405
-- title:
--   Lemma B.2: an element of $\mathcal W$ is the joint law of two successive demands
-- statement:
--   If $w\in\mathcal W$, then for all $t,q$ and $k$,
--
--   $$
--   w^k_t(q)=P\{D^k\ge t,\ D^{k-1}=q\}.
--   $$
--
--   So $\mathcal W$ has a single element, and it records the joint distribution of the demands in a pair of successive stages.
--
--   Differences from the source:
--   - encoding: stages $1,\dots,K$, periods and demands $1,\dots,T$ → 0-based indices `Fin K`, `Fin T`; reason: relabelling; the stated bounds translate each exponent accordingly
--   - encoding: the survival rate $\theta^k_t(q)$ is the primitive of the demand process → the transition law `trans` is primitive and $\theta$ is derived from it; reason: equivalent data
--   - generalization: the standing transition assumption $P\{D^{k+1}=p\mid D^k=q\}\ge\epsilon$ of §2, p.7 → no assumption on the transition law of the demands; reason: the induction over $\mathcal W$ uses only the definition of $\theta$ and the Markov property; every instance of the source is covered
-- source:
--   Li, Rusmevichientong & Topaloglu, Revenue Management with Calendar-Aware and Dependent Demands, arXiv:2409.02637v2, Lemma B.2, ER p.5 (PDF 27)

import Mathlib
import Definitions.Def_CalendarDependentRM_Instance_IsFeasible12

namespace CalendarDependentRM

/-- **Lemma B.2.** Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, Lemma B.2, Extended Results p. 5 (PDF p. 27):
if `w ∈ 𝒲`, then `w^k_t(q) = P{D^k ≥ t, D^{k-1} = q}` for all `t`, `q`, `k`.

**Formalization Note** `k`, `t`, `q` are 0-based; `C.reach k t q` is the event `{D^k ≥ t, D^{k-1} = q}`. -/
theorem lemma_B_2 {K T : ℕ} (C : DemandChain K T) {w : Fin K → Fin T → Fin T → ℝ} (hw : C.IsW w)
    (k : Fin K) (t q : Fin T) :
    w k t q = C.prob (C.reach k t q) := by sorry

end CalendarDependentRM
