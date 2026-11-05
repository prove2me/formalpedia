-- Prove2me | Theorems.Thm_CalendarDependentRM_lemma_B_1
-- name    : CalendarDependentRM.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:59.025381+00:00
-- url     : https://prove2.me/theorems/a1deb014-dbd6-4e61-afe8-8a62eabf4da6
-- title:
--   Lemma B.1: the relaxed value functions are linear in the capacities
-- statement:
--   With the slopes $\alpha^k_{it}(q;\mu)$ and intercepts $\beta^k_t(q;\mu)$ of (10), the value functions of the relaxed dynamic program (9) are linear in the capacities:
--
--   $$
--   \tilde J^k_t(y,q;\mu)=\sum_{i\in\mathcal L}\alpha^k_{it}(q;\mu)y_i+\beta^k_t(q;\mu)
--   $$
--
--   for all $t$ and $k$. This turns the minimization over $\mu$ into the linear program (11).
--
--   Differences from the source:
--   - encoding: the domain of $y$ in (9) is left implicit → every integer vector $y$; reason: the recursion of (9) has no capacity constraint and reaches negative capacities, so the integer vectors are its natural domain; nonnegative $y$ are a special case
--   - encoding: stages $1,\dots,K$, periods and demands $1,\dots,T$ → 0-based indices `Fin K`, `Fin T`; reason: relabelling; the stated bounds translate each exponent accordingly
--   - encoding: the survival rate $\theta^k_t(q)$ is the primitive of the demand process → the transition law `trans` is primitive and $\theta$ is derived from it; reason: equivalent data
--   - generalization: the standing transition assumption $P\{D^{k+1}=p\mid D^k=q\}\ge\epsilon$ of §2, p.7 → no assumption on the transition law of the demands; reason: the identity follows from (9) and (10) by induction and uses no property of the transitions; every instance of the source is covered
-- source:
--   Li, Rusmevichientong & Topaloglu, Revenue Management with Calendar-Aware and Dependent Demands, arXiv:2409.02637v2, Lemma B.1, ER p.4 (PDF 26)

import Mathlib
import Definitions.Def_CalendarDependentRM_Instance_Jtilde

namespace CalendarDependentRM

/-- **Lemma B.1.** Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, Lemma B.1, Extended Results p. 4 (PDF p. 26):
with `α^k_it(q; µ)`, `β^k_t(q; µ)` as in (10), the value functions of (9) are linear in the capacities,
`J̃^k_t(y, q; µ) = Σ_i α^k_it(q; µ) y_i + β^k_t(q; µ)` for all `t`, `k`.

**Formalization Note** `k`, `t` are 0-based. The identity holds for every integer vector `y` and every `µ`, as in the
paper, whose proof puts no sign on either. -/
theorem lemma_B_1 {R J : Type*} [Fintype R] [Fintype J] {K T : ℕ} (I : Instance R J K T)
    (μ : Fin K → R → Fin T → Fin T → ℝ) (k : Fin K) (t : Fin T) (y : R → ℤ) (q : Fin T) :
    I.Jtilde μ k t y q = ∑ i, I.alpha μ k t i q * (y i : ℝ) + I.beta μ k t q := by sorry

end CalendarDependentRM
