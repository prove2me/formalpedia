-- Prove2me | Theorems.Thm_ComplexityUnpred_Catalytic_observation_4_15
-- name    : ComplexityUnpred.Catalytic.observation_4_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:04:32.584939+00:00
-- url     : https://prove2.me/theorems/faffcd27-37b3-4122-80a9-be8b54430a7f
-- title:
--   Observation 4.15 — G(C, D, M) is a deterministic hypercube digraph
-- statement:
--   Let $(C,D)$ be a LossyCoding instance, $C:\{0,1\}^n\to\{0,1\}^{n-1}$, $D:\{0,1\}^{n-1}\to\{0,1\}^n$, and let $M$ be an in-place machine with state size $\ell$ that computes $D^{\mathrm{ext}}(x)=D(x_{<n})$. Then the graph $G(C,D,M)=(V,E,\mathrm{lab},\mathrm{ind})$ of Definition 4.14 — the computation paths of $M$ from the inputs $C(x)\circ b$, $x\in\mathrm{NonSol}(C,D)$, $b\in\{0,1\}$, with labels $\sigma\circ b$ and $\mathrm{ind}(l)=\text{input-head}(l_{\le\ell})$ — is a deterministic hypercube digraph of dimension $n$ with $(\ell+1)$-bit labels:
--   $$\#\{e\in E:\ e\text{ leaves }v,\ \mathrm{lab}(e)=l\}\le1\quad\text{and}\quad \{i: v_i\ne v'_i\}\subseteq\{\mathrm{ind}(\mathrm{lab}(e))\}\ \text{for every edge }e=(v,v').$$
--
--   With Lemma 4.16 it makes WeakExcess on $G(C,D,M)$ a correct target for LossyCoding.
--
--   **Formalization Note** `(lossyGraph C D M).IsDeterministic`; the machine is an `InPlaceMachine n ℓ` and `M.ComputesDext D` says it halts on every $y\in\{0,1\}^n$ with $D^{\mathrm{ext}}(y)$ on its input tape.
--
--   Differences from the source:
--   - generalization: an in-place Turing machine M computing D^ext, with state size ℓ → any InPlaceMachine n ℓ (deterministic step on (y, σ) with σ ∈ {0,1}^ℓ, start state, halting states, input head, a step changes y only under the input head) computing D^ext; reason: every in-place Turing machine with an injective ℓ-bit code of its states is one, so the statement specializes to the paper's
--   - encoding: time(M(y)), the number of steps before halting → InPlaceMachine.time := sInf of the halting times; reason: equal to the paper's time whenever M halts, which ComputesDext assumes for every input
--   - encoding: strings in {0,1}ⁿ, indices in [n] = {1, …, n} → Fin n → Bool, 0-based indices Fin n; reason: Lean convention; same instances
-- source:
--   Agarwala, Dorfman, The Complexity of Unpredictability, arXiv:2611.05956v1, p. 36, Observation 4.15

import Mathlib
import Definitions.Def_ComplexityUnpred_Catalytic_LossyCoding

namespace ComplexityUnpred.Catalytic

/-- **Observation 4.15** (Agarwala, Dorfman, arXiv:2611.05956v1, p. 36): for a pair (C, D)
of LossyCoding maps and an in-place machine M with ℓ-bit states computing D^ext, G(C, D, M)
is a deterministic hypercube digraph of dimension n with (ℓ + 1)-bit labels. -/
theorem observation_4_15 {n ℓ : ℕ} (C : (Fin n → Bool) → Fin (n - 1) → Bool)
    (D : (Fin (n - 1) → Bool) → Fin n → Bool) (M : InPlaceMachine n ℓ)
    (hM : M.ComputesDext D) :
    (lossyGraph C D M).IsDeterministic := by sorry

end ComplexityUnpred.Catalytic
