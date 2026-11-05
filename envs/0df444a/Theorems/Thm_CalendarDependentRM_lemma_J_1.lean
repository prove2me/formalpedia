-- Prove2me | Theorems.Thm_CalendarDependentRM_lemma_J_1
-- name    : CalendarDependentRM.lemma_J_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:35:57.551774+00:00
-- url     : https://prove2.me/theorems/81a5138d-9844-4fb8-84cf-a78167025e09
-- title:
--   Lemma J.1: geometric decay of the dependence between stages
-- statement:
--   Assume the transition assumption with $\epsilon>0$. For all $p,q$ and stages $k<\ell$,
--
--   $$
--   P\{D^\ell=q\mid D^k=p\}-P\{D^\ell=q\}=(1-\epsilon)^{\ell-k}\big[P\{Y^\ell=q\mid Y^k=p\}-P\{D^\ell=q\}\big],
--   $$
--
--   where $Y$ is the auxiliary non-stationary chain with the transition kernel $Q$ of (22). This extends a classical mixing-time argument to non-stationary chains, and the factor $(1-\epsilon)^{\ell-k}$ drives the martingale bound.
--
--   Differences from the source:
--   - encoding: $Q^k$ in (22) has the factor $1/\theta$ with $\theta=1-\epsilon$ → at $\epsilon=1$, Lean reads $1/0=0$, so $Q=0$; reason: at $\epsilon=1$ the transition assumption forces $T=1$ and both sides of the identity vanish
--   - encoding: $P\{D^\ell=q\mid D^k=p\}$ and $P\{Y^\ell=q\mid Y^k=p\}$ → the multi-step kernels `multiStep C.trans` and `multiStep (C.Qker ε)`; reason: the paper's proof computes them through Chapman–Kolmogorov; as ratios they would read $0$ at a null $\{D^k=p\}$ of stage one, where the identity would fail under the literal transition assumption
--   - reading: $P\{D^{k+1}=p\mid D^k=q\}\ge\epsilon$ for all $p,q\in\mathcal T$, $k\in\mathcal K$ → the bound holds for the transitions between stages of the horizon, into stages $2,\dots,K$, with no condition on $D^1$ given $\hat D^0$; reason: at $k=K$ the printed condition names a nonexistent $D^{K+1}$; this literal reading is the weakest hypothesis, so the result covers every other reading
--   - encoding: stages $1,\dots,K$, periods and demands $1,\dots,T$ → 0-based indices `Fin K`, `Fin T`; reason: relabelling; the stated bounds translate each exponent accordingly
--   - encoding: the survival rate $\theta^k_t(q)$ is the primitive of the demand process → the transition law `trans` is primitive and $\theta$ is derived from it; reason: equivalent data
-- source:
--   Li, Rusmevichientong & Topaloglu, Revenue Management with Calendar-Aware and Dependent Demands, arXiv:2409.02637v2, Lemma J.1, ER p.20 (PDF 42)

import Mathlib
import Definitions.Def_CalendarDependentRM_DemandChain_Qker

namespace CalendarDependentRM

/-- **Lemma J.1.** Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, Lemma J.1, Extended Results p. 20 (PDF p. 42):
for all `p`, `q` and `k`, `ℓ` with `ℓ ≥ k + 1`,
`P{D^ℓ = q | D^k = p} − P{D^ℓ = q} = (1 − ε)^{ℓ−k} [P{Y^ℓ = q | Y^k = p} − P{D^ℓ = q}]`.

**Formalization Note** The conditional probabilities are in kernel form: `multiStep C.trans` for `D` and
`multiStep (C.Qker ε)` for the chain `Y` of (22). Under `Minorized`, which says nothing on stage one, `P{D^k = p}` may
vanish at stage one, and the kernel is the meaning the paper's proof uses. At `ε = 1`, which forces `T = 1`, both sides
vanish. -/
theorem lemma_J_1 {K T : ℕ} (C : DemandChain K T) {ε : ℝ} (hε : 0 < ε) (hmin : C.Minorized ε)
    (k ℓ : Fin K) (hkℓ : k < ℓ) (p q : Fin T) :
    DemandChain.multiStep C.trans k ((ℓ : ℕ) - k) p q - C.marginal ℓ q =
      (1 - ε) ^ ((ℓ : ℕ) - k) * (DemandChain.multiStep (C.Qker ε) k ((ℓ : ℕ) - k) p q - C.marginal ℓ q) := by sorry

end CalendarDependentRM
