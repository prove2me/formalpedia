-- Prove2me | Theorems.Thm_ComplexityUnpred_Catalytic_observation_4_17
-- name    : ComplexityUnpred.Catalytic.observation_4_17
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:04:40.281052+00:00
-- url     : https://prove2.me/theorems/b06e6fab-fb2f-468a-93f4-a057ad144de3
-- title:
--   Observation 4.17 — characterization of EdgeExists(v, l) on G(C, D, M)
-- statement:
--   Let $(C,D)$ be a LossyCoding instance, $M$ an in-place machine computing $D^{\mathrm{ext}}$ with state size $\ell$, $v\in\{0,1\}^n$ a vertex of $G(C,D,M)$ and $l\in\{0,1\}^{\ell+1}$ a label. Then $\mathrm{EdgeExists}(v,l)$ holds on $G(C,D,M)$ if and only if
--
--   1. there exist $y\in\mathrm{NonSol}(C,D)$ and $0\le t<\mathrm{time}(M(C(y)\circ l_{\ell+1}))$ with
--   $$M^{(t)}(C(y)\circ l_{\ell+1},\sigma_{\mathrm{start}})=(v,l_{\le\ell}),$$
--   2. and $M(v,l_{\le\ell})_1\neq v$ (the edge is not a self-loop).
--
--   It is what makes $\mathrm{EdgeExists}$ on $G(C,D,M)$ decidable by a polynomial-size circuit in Theorem 4.18.
--
--   **Formalization Note** $l_{\ell+1}$ is `l (Fin.last ℓ)`, $l_{\le\ell}$ is `initLabel l`, $C(y)\circ b$ is `snocBit (C y) b`.
--
--   Differences from the source:
--   - generalization: an in-place Turing machine M computing D^ext, with state size ℓ → any InPlaceMachine n ℓ (deterministic step on (y, σ) with σ ∈ {0,1}^ℓ, start state, halting states, input head, a step changes y only under the input head) computing D^ext; reason: every in-place Turing machine with an injective ℓ-bit code of its states is one, so the statement specializes to the paper's
--   - encoding: time(M(y)), the number of steps before halting → InPlaceMachine.time := sInf of the halting times; reason: equal to the paper's time whenever M halts, which ComputesDext assumes for every input
--   - encoding: strings in {0,1}ⁿ, indices in [n] = {1, …, n} → Fin n → Bool, 0-based indices Fin n; reason: Lean convention; same instances
-- source:
--   Agarwala, Dorfman, The Complexity of Unpredictability, arXiv:2611.05956v1, p. 37, Observation 4.17

import Mathlib
import Definitions.Def_ComplexityUnpred_Catalytic_LossyCoding

namespace ComplexityUnpred.Catalytic

/-- **Observation 4.17** (Agarwala, Dorfman, arXiv:2611.05956v1, p. 37): characterization of
EdgeExists(v, l) on G(C, D, M) by a computation path of M from some C(y) followed by the last
bit of l, with y in NonSol(C, D), passing through the configuration (v, first ℓ bits of l), plus
the condition that the next step changes the input tape (no self-loop). -/
theorem observation_4_17 {n ℓ : ℕ} (C : (Fin n → Bool) → Fin (n - 1) → Bool)
    (D : (Fin (n - 1) → Bool) → Fin n → Bool) (M : InPlaceMachine n ℓ)
    (hM : M.ComputesDext D) (v : Fin n → Bool) (l : Fin (ℓ + 1) → Bool) :
    (lossyGraph C D M).EdgeExists v l ↔
      (∃ y ∈ NonSol C D, ∃ t < M.time (snocBit (C y) (l (Fin.last ℓ))),
          M.run t (snocBit (C y) (l (Fin.last ℓ)), M.start) = (v, initLabel l)) ∧
        (M.step (v, initLabel l)).1 ≠ v := by sorry

end ComplexityUnpred.Catalytic
