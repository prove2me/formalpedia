-- Prove2me | Theorems.Thm_CalendarDependentRM_relaxed_dominates
-- name    : CalendarDependentRM.relaxed_dominates
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:37:15.375213+00:00
-- url     : https://prove2.me/theorems/1783060c-5bcf-48df-bd40-ff97f0917ef2
-- title:
--   §B: the relaxed dynamic program dominates (1), for $\mu\ge0$
-- statement:
--   Let $\mu=(\mu^k_{it}(q))\ge0$ be Lagrange multipliers. Then the value functions of the relaxed dynamic program (9) bound those of the dynamic program (1) from above: for all stages $k$, periods $t$, capacity vectors $y\in\mathbb Z_+^{|\mathcal L|}$ and previous demands $q$,
--
--   $$
--   \tilde J^k_t(y,q;\mu)\ge J^k_t(y,q).
--   $$
--
--   Minimizing $\tilde J^1_1(c,\hat D^0;\mu)$ over $\mu\ge0$ therefore gives an upper bound on the optimal total expected revenue. This is the first step towards Theorem 3.1.
--
--   Differences from the source:
--   - encoding: stages $1,\dots,K$, periods and demands $1,\dots,T$ → 0-based indices `Fin K`, `Fin T`; reason: relabelling; the stated bounds translate each exponent accordingly
--   - encoding: the survival rate $\theta^k_t(q)$ is the primitive of the demand process → the transition law `trans` is primitive and $\theta$ is derived from it; reason: equivalent data
--   - generalization: the standing transition assumption $P\{D^{k+1}=p\mid D^k=q\}\ge\epsilon$ of §2, p.7 → no assumption on the transition law of the demands; reason: the induction over (1) and (9) uses only $\mu\ge0$ and $a_{ij}u_j\le y_i$ for $u\in\mathcal F(y)$; every instance of the source satisfies the Lean hypotheses
-- source:
--   Li, Rusmevichientong & Topaloglu, Revenue Management with Calendar-Aware and Dependent Demands, arXiv:2409.02637v2, §B, ER p.3 (PDF 25), unnumbered

import Mathlib
import Definitions.Def_CalendarDependentRM_Instance_Jtilde

namespace CalendarDependentRM

/-- **The relaxed dynamic program dominates (1).** Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, §B,
Extended Results p. 3 (PDF p. 25), unnumbered: for `µ ≥ 0`, `J̃^k_t(y, q; µ) ≥ J^k_t(y, q)` for all `y ∈ ℤ₊^{|𝓛|}`, `q`.

**Formalization Note** `k`, `t` are 0-based. `y` is cast from naturals into the integer state of `Jtilde`. The
paper states this as a standard fact without proof. -/
theorem relaxed_dominates {R J : Type*} [Fintype R] [Fintype J] {K T : ℕ} (I : Instance R J K T)
    (μ : Fin K → R → Fin T → Fin T → ℝ) (hμ : ∀ k i t q, 0 ≤ μ k i t q) (k : Fin K) (t : Fin T)
    (y : R → ℕ) (q : Fin T) :
    I.valueFn k t y q ≤ I.Jtilde μ k t (fun i => (y i : ℤ)) q := by sorry

end CalendarDependentRM
