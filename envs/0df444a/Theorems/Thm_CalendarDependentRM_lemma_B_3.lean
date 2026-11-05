-- Prove2me | Theorems.Thm_CalendarDependentRM_lemma_B_3
-- name    : CalendarDependentRM.lemma_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:49.031625+00:00
-- url     : https://prove2.me/theorems/fdd69baf-c298-4839-841c-1e5454062b16
-- title:
--   Lemma B.3: an identity for feasible solutions of (12)
-- statement:
--   Let $(y,u,w)$ be a feasible solution of the linear program (12). Then for all $i,t,q$ and $k$,
--
--   $$
--   P\{D^k\ge t,D^{k-1}=q\}c_i-\sum_{\ell=1}^{k-1}\sum_s\sum_p\sum_ja_{ij}P\{D^k\ge t,D^{k-1}=q\mid D^\ell\ge s,D^{\ell-1}=p\}u^\ell_{js}(p)-\sum_{s=1}^t\sum_ja_{ij}P\{D^k\ge t\mid D^k\ge s,D^{k-1}=q\}u^k_{js}(q)=y^k_{it}(q).
--   $$
--
--   Since $y\ge0$, the left side is nonnegative, and this is what links (12) to the conditional capacity constraints of the fluid approximation.
--
--   Differences from the source:
--   - encoding: stages $1,\dots,K$, periods and demands $1,\dots,T$ → 0-based indices `Fin K`, `Fin T`; reason: relabelling; the stated bounds translate each exponent accordingly
--   - encoding: the survival rate $\theta^k_t(q)$ is the primitive of the demand process → the transition law `trans` is primitive and $\theta$ is derived from it; reason: equivalent data
--   - encoding: conditional probabilities given a null event are undefined → they read $0$ (a ratio with $0/0=0$), or the zero measure for `cond`; reason: this only concerns states the policy never reaches, and such states have zero objective coefficient
--   - generalization: the standing transition assumption $P\{D^{k+1}=p\mid D^k=q\}\ge\epsilon$ of §2, p.7 → no assumption on the transition law of the demands; reason: the induction over the constraints of (12) uses Bayes' rule and the Markov property only; every instance of the source is covered
-- source:
--   Li, Rusmevichientong & Topaloglu, Revenue Management with Calendar-Aware and Dependent Demands, arXiv:2409.02637v2, Lemma B.3, ER p.6 (PDF 28)

import Mathlib
import Definitions.Def_CalendarDependentRM_Instance_IsFeasible12

namespace CalendarDependentRM

/-- **Lemma B.3.** Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, Lemma B.3, Extended Results p. 6 (PDF p. 28):
for a feasible solution `(y, u, w)` of (12) and all `i`, `t`, `q`, `k`,
`P{D^k ≥ t, D^{k-1} = q} c_i − Σ_{ℓ=1}^{k-1} Σ_s Σ_p Σ_j a_ij P{D^k ≥ t, D^{k-1} = q | D^ℓ ≥ s, D^{ℓ-1} = p} u^ℓ_js(p)
− Σ_{s=1}^t Σ_j a_ij P{D^k ≥ t | D^k ≥ s, D^{k-1} = q} u^k_js(q) = y^k_it(q)`.

**Formalization Note** 0-based indices. A conditional probability given a null event reads `0`
(`DemandChain.condProb`); there `u = 0` by `u ≤ λ w` and Lemma B.2, so the term is `0` either way. -/
theorem lemma_B_3 {R J : Type*} [Fintype J] {K T : ℕ} (I : Instance R J K T)
    {y : Fin K → R → Fin T → Fin T → ℝ} {u : Fin K → J → Fin T → Fin T → ℝ}
    {w : Fin K → Fin T → Fin T → ℝ} (h : I.IsFeasible12 y u w) (i : R) (k : Fin K) (t q : Fin T) :
    I.chain.prob (I.chain.reach k t q) * (I.c i : ℝ) -
        (∑ ℓ ∈ Finset.univ.filter (fun ℓ : Fin K => ℓ < k), ∑ s, ∑ p, ∑ j,
          (I.a i j : ℝ) * I.chain.condProb (I.chain.reach k t q) (I.chain.reach ℓ s p) * u ℓ j s p) -
        ∑ s ∈ Finset.Iic t, ∑ j,
          (I.a i j : ℝ) * I.chain.condProb (fun d => t ≤ d k) (I.chain.reach k s q) * u k j s q =
      y k i t q := by sorry

end CalendarDependentRM
