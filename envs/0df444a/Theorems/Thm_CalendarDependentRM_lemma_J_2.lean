-- Prove2me | Theorems.Thm_CalendarDependentRM_lemma_J_2
-- name    : CalendarDependentRM.lemma_J_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:35:10.453099+00:00
-- url     : https://prove2.me/theorems/30c82c6b-a417-48d2-b356-da357f0f3e5a
-- title:
--   Lemma J.2: the total variation gap of a pair of successive demands
-- statement:
--   Assume the transition assumption with $\epsilon>0$. For all $q,s$ and stages $k<\ell$,
--
--   $$
--   \sum_{p}\big|P\{D^k\ge s,D^{k-1}=p\mid D^\ell=q\}-P\{D^k\ge s,D^{k-1}=p\}\big|\le\frac1\epsilon(1-\epsilon)^{\ell-k}.
--   $$
--
--   So conditioning on a later demand changes the law of an earlier pair of demands by a geometrically small amount.
--
--   Differences from the source:
--   - encoding: for all $p,q,s\in\mathcal T$, with $\sum_{p\in\mathcal T}$ on the left → for all $q,s$; reason: $p$ is the summation variable
--   - reading: $P\{D^{k+1}=p\mid D^k=q\}\ge\epsilon$ for all $p,q\in\mathcal T$, $k\in\mathcal K$ → the bound holds for the transitions between stages of the horizon, into stages $2,\dots,K$, with no condition on $D^1$ given $\hat D^0$; reason: at $k=K$ the printed condition names a nonexistent $D^{K+1}$; this literal reading is the weakest hypothesis, so the result covers every other reading
--   - encoding: stages $1,\dots,K$, periods and demands $1,\dots,T$ → 0-based indices `Fin K`, `Fin T`; reason: relabelling; the stated bounds translate each exponent accordingly
--   - encoding: the survival rate $\theta^k_t(q)$ is the primitive of the demand process → the transition law `trans` is primitive and $\theta$ is derived from it; reason: equivalent data
-- source:
--   Li, Rusmevichientong & Topaloglu, Revenue Management with Calendar-Aware and Dependent Demands, arXiv:2409.02637v2, Lemma J.2, ER p.21 (PDF 43)

import Mathlib
import Definitions.Def_CalendarDependentRM_DemandChain

namespace CalendarDependentRM

/-- **Lemma J.2.** Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, Lemma J.2, Extended Results p. 21 (PDF p. 43):
for all `q`, `s` and `k`, `ℓ` with `ℓ ≥ k + 1`,
`Σ_p |P{D^k ≥ s, D^{k-1} = p | D^ℓ = q} − P{D^k ≥ s, D^{k-1} = p}| ≤ (1/ε)(1 − ε)^{ℓ−k}`.

**Formalization Note** 0-based indices. `ℓ` is never the first stage, so `P{D^ℓ = q} ≥ ε > 0` by `Minorized`. The printed
quantifier also lists `p`, which is the summation variable. -/
theorem lemma_J_2 {K T : ℕ} (C : DemandChain K T) {ε : ℝ} (hε : 0 < ε) (hmin : C.Minorized ε)
    (k ℓ : Fin K) (hkℓ : k < ℓ) (s q : Fin T) :
    ∑ p, |C.condProb (C.reach k s p) (fun d => d ℓ = q) - C.prob (C.reach k s p)| ≤
      (1 / ε) * (1 - ε) ^ ((ℓ : ℕ) - k) := by sorry

end CalendarDependentRM
