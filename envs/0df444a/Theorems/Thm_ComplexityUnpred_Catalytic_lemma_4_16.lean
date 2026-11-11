-- Prove2me | Theorems.Thm_ComplexityUnpred_Catalytic_lemma_4_16
-- name    : ComplexityUnpred.Catalytic.lemma_4_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:04:12.924576+00:00
-- url     : https://prove2.me/theorems/8ba6a9e7-d18f-4174-9272-9ed10de507f8
-- title:
--   Lemma 4.16 — every WeakExcess solution of G(C, D, M) is a LossyCoding solution of (C, D)
-- statement:
--   Let $(C,D)$ be a LossyCoding instance with $C:\{0,1\}^n\to\{0,1\}^{n-1}$ and $D:\{0,1\}^{n-1}\to\{0,1\}^n$, let $M$ be an in-place machine computing $D^{\mathrm{ext}}$, $\ell$ its state size, and $G=G(C,D,M)$ (Definition 4.14). Then every vertex $v\in\{0,1\}^n$ with
--   $$\text{out-degree}_G(v)\ge\text{in-degree}_G(v)\quad\text{satisfies}\quad D(C(v))\ne v,$$
--   i.e. every solution to WeakExcess on $G$ is a solution to LossyCoding on $(C,D)$.
--
--   This is the correctness half of the reduction from LossyCoding to WeakExcess (Theorem 4.18).
--
--   **Formalization Note** Degrees count edge copies of the multiset $E$ (walks of length $0$, when $\mathrm{time}(M(C(x)\circ b))=0$, contribute no edge).
--
--   Differences from the source:
--   - generalization: an in-place Turing machine M computing D^ext, with state size ℓ → any InPlaceMachine n ℓ (deterministic step on (y, σ) with σ ∈ {0,1}^ℓ, start state, halting states, input head, a step changes y only under the input head) computing D^ext; reason: every in-place Turing machine with an injective ℓ-bit code of its states is one, so the statement specializes to the paper's
--   - encoding: time(M(y)), the number of steps before halting → InPlaceMachine.time := sInf of the halting times; reason: equal to the paper's time whenever M halts, which ComputesDext assumes for every input
--   - encoding: strings in {0,1}ⁿ, indices in [n] = {1, …, n} → Fin n → Bool, 0-based indices Fin n; reason: Lean convention; same instances
-- source:
--   Agarwala, Dorfman, The Complexity of Unpredictability, arXiv:2611.05956v1, p. 36, Lemma 4.16

import Mathlib
import Definitions.Def_ComplexityUnpred_Catalytic_LossyCoding

namespace ComplexityUnpred.Catalytic

/-- **Lemma 4.16** (Agarwala, Dorfman, arXiv:2611.05956v1, p. 36). For a LossyCoding instance
`(C, D)` and an in-place machine `M` with `ℓ`-bit states computing `D^ext`, every vertex `v` of
`G(C, D, M)` with `out-degree(v) ≥ in-degree(v)` satisfies `D(C(v)) ≠ v`. -/
theorem lemma_4_16 {n ℓ : ℕ} (C : (Fin n → Bool) → Fin (n - 1) → Bool)
    (D : (Fin (n - 1) → Bool) → Fin n → Bool) (M : InPlaceMachine n ℓ)
    (hM : M.ComputesDext D) (v : Fin n → Bool)
    (hv : (lossyGraph C D M).inDeg v ≤ (lossyGraph C D M).outDeg v) :
    D (C v) ≠ v := by sorry

end ComplexityUnpred.Catalytic
