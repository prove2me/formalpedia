-- Prove2me | Theorems.Thm_BeyondDS_Supplement_theorem_9
-- name    : BeyondDS.Supplement.theorem_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T05:13:00.522143+00:00
-- url     : https://prove2.me/theorems/b55051cf-54cf-4c34-af44-4e9fd0afb078
-- title:
--   Theorem 9 — capped adaptive agreement with grinding: failure $\le\Delta+q\rho^V$, $\mathbb E[T]\le3+4(z+8e+V\Delta)$, $\mathbb E[M]\le n\ell(7+4z+32e+4V\Delta)$
-- statement:
--   Work in the model of §10.1: $n$ players, an adaptive rushing adversary corrupting at most $f\le(\tfrac12-\varepsilon)n$ players in total with $0<\varepsilon<\tfrac12$ and $\varepsilon n\ge8$; ideal eligibility evaluations for every registered key; atomic eligibility-and-multicast actions; an even committee parameter $\ell$ with $2\le\ell\le n$ and certificate threshold $\ell/2$; $V\ge1$ ordinary iterations; and $q\ge1$ candidate registration domains among which the adversary selects after inspecting its own evaluations. Let $\epsilon_{\mathrm{auth}}\ge0$ bound the probability that signature or eligibility-proof authenticity fails during the capped execution, and define
--   $$\Delta_0=12\,q\,(V+1)^2\exp(-\varepsilon^2\ell/16),\qquad \Delta=\Delta_0+\epsilon_{\mathrm{auth}},\qquad \rho=1-\frac{1}{8e},\qquad z=\Big\lceil\frac{\log q}{-\log\rho}\Big\rceil .$$
--
--   Consider the protocol of §10.2 in either alternative: the erasure alternative with arbitrary values, or the alternative without erasures with binary values and value-specific eligibility. For every input assignment and every adversary:
--
--   1. On every execution, no honest player is active after round $4V+3$, every forever-honest player has decided, and $M\le(4V+3)\,n(n-1)$.
--   2. Agreement and strong unanimity fail with probability at most
--   $$\Delta+q\rho^{V}.$$
--   3. If $T$ is the time by which no honest player remains active and $M$ is the number of point-to-point messages sent while their senders are honest, including all terminal messages, then
--   $$\mathbb E[T]\le 3+4\,(z+8e+V\Delta),\qquad \mathbb E[M]\le n\ell\,(7+4z+32e+4V\Delta).$$
--
--   The dependence on the grinding budget $q$ is explicit: it enters the error through $q\rho^V$ and the expected latency and communication through $z=O(1+\log q)$.
--
--   **Formalization Note** The model and the protocol are `sexec`. Signatures and eligibility proofs are ideal: every token an honest player examines verifies, a token that is not authentic is a forgery, and $\epsilon_{\mathrm{auth}}$ bounds the probability that an honest player accepts a message containing one. The evaluations stay independent and uniform on failure histories. Logarithms are natural and $z$ is a natural number. Expectations are in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: signatures and eligibility proofs under a security assumption; ϵ_auth bounds the probability that their authenticity fails → ideal tokens: every examined token verifies, a token that is not authentic is a forgery recorded by a flag, and ϵ_auth ≥ 0 is any bound on the probability of the flag; reason: the source treats authenticity only through this event and its probability; an execution with real schemes is an execution of this model with the same event
--   - encoding: oracle evaluations normalized to uniform Y ∈ [0, 1], at arbitrary inputs → evaluations uniform on the grid {0, …, n − 1}, at the labels of the protocol; reason: eligibility has exactly the probabilities ℓ/n and 1/n; evaluations at other inputs are independent of the execution
--   - reading: registration with at most q distinct canonical candidate domains processed before selection, each with fresh independent tables → q candidate domains with independent tables; the adversary may corrupt adaptively during registration, sees every corrupted key's evaluations in all q domains, and then selects one; reason: this is the experiment the proof analyses (a union bound over the q candidates); corruptions made during registration count toward f
--   - reading: "one fixed public total order on the finite encodings being compared" → tie-breaking by arbitrary injective keys into ℕ, universally quantified; reason: the source fixes no particular order; the statement holds for each
--   - reading: erasure of the phase key "after each completed eligibility action" → a corrupted signer's token is a forgery only if the signer completed an eligibility action for that very label while honest; reason: the source leaves open whether keys of skipped phases are erased ("the proof does not require a separate erasure action"); this reading counts fewer tokens as forgeries, so the bounds are the stronger ones
--   - generalization: the alternative without erasures "permits binary values" → any value type with an injective tag into the two bits, which includes Bool; reason: a type that injects into the bits has at most two values; Bool with the identity tag is the source's case
--   - encoding: "The protocol halts within 4V + 3 rounds on every execution" → on every execution T ≤ 4V + 3, every never-corrupted player is inactive and has decided; reason: the same assertion written out
-- source:
--   Rambaud, Beyond Dolev–Strong: Adaptive Byzantine Broadcast with Õ(n^{3/2}) Messages at a Tight Honest Majority, STOC 2027 submission (manuscript sha256 c84cf9c9…), Theorem 9, p.43 (PDF p.44), eqs. (47)–(50); §10.1, pp.37–38 (PDF pp.38–39); §10.2, pp.38–40 (PDF pp.39–41)

import Mathlib
import Definitions.Def_BeyondDS_Supplement_Sortition

set_option autoImplicit false

open scoped ENNReal

namespace BeyondDS.Supplement

open BeyondDS

/-- Theorem 9 (Capped adaptive agreement with grinding), Rambaud, *Beyond Dolev–Strong*, STOC 2027 submission (manuscript sha256 c84cf9c9…), p.43 (PDF 44): "In the model of Section 10.1, define Δ₀ = 12q(V + 1)² exp(−ε²ℓ/16), Δ = Δ₀ + ϵ_auth, ρ = 1 − 1/(8e). (47) The protocol halts within 4V + 3 rounds on every execution and satisfies agreement and strong unanimity with failure probability at most η ≤ Δ + qρ^V. (48) Put z = ⌈log q/(− log ρ)⌉. If T is the time by which no honest player remains active and M is the number of point-to-point messages sent while their senders are honest, including all terminal messages, then E[T] ≤ 3 + 4(z + 8e + VΔ), (49) E[M] ≤ nℓ(7 + 4z + 32e + 4VΔ). (50) The erasure alternative permits arbitrary values; the alternative without erasures permits binary values and uses value-specific eligibility. The deterministic message cap is (4V + 3)n(n − 1) ≤ (4V + 3)n²."

Hypotheses of §10.1 (pp.37–38): `n` players, at most `f ≤ (1/2 − ε)n` adaptive corruptions with `0 < ε < 1/2` and `εn ≥ 8`; `ℓ` even with `2 ≤ ℓ ≤ n`; `V ≥ 1` ordinary iterations; `q ≥ 1` candidate domains. The protocol is that of §10.2 (`sexec`), in either alternative: the erasure alternative (labels without a value, phase keys erased, any value type) or the alternative without erasures (value-specific labels, at most two values). For every tie-breaking order, default value, input assignment and adversary, with `ϵ_auth ≥ 0` any bound on the probability of the authenticity failure of this execution:

1. on every execution, no honest player is active after round `4V + 3`, every forever-honest player has decided, and `M ≤ (4V + 3)n(n − 1)`;
2. agreement and strong unanimity fail with probability at most `Δ + qρ^V`;
3. `E[T] ≤ 3 + 4(z + 8e + VΔ)` and `E[M] ≤ nℓ(7 + 4z + 32e + 4VΔ)`.

**Formalization Note.** Signatures and eligibility proofs are ideal objects: every token an honest player examines verifies, and a token that is not authentic (`SCfg.legit`) is a forgery, recorded by `authFail`; `ϵ_auth` bounds the probability of that event, as in the source ("Let ϵ_auth bound the probability that signature or eligibility-proof authenticity fails during the entire capped execution"). The evaluations of all keys in all `q` candidate domains are independent and uniform, and stay so on failure histories. Logarithms are natural; `z` is a natural-number ceiling. Expectations are in `[0, ∞]` and hold for every adversary. -/
theorem theorem_9 (n f ell V q : ℕ) [NeZero n] (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1 / 2)
    (hf : (f : ℝ) ≤ (1 / 2 - ε) * n) (hεn : 8 ≤ ε * n) (hell : Even ell) (hell2 : 2 ≤ ell)
    (helln : ell ≤ n) (hV : 1 ≤ V) (hq : 1 ≤ q)
    (Val : Type) [DecidableEq Val] (alt : Alt Val)
    (halt : (alt.erase = true ∧ ∀ v, alt.tag v = none) ∨
      (alt.erase = false ∧ Function.Injective alt.tag ∧ ∀ v, alt.tag v ≠ none))
    (T : Ties n Val) (hT : Function.Injective T.vc ∧ Function.Injective T.prop ∧ Function.Injective T.cc)
    (v₀ : Val) (x : Fin n → Val) (A : SAdv n q V Val) (εa : ℝ) (hεa0 : 0 ≤ εa)
    (hεa : prob (sexec alt T f ell v₀ x A) {ω | ω.authFail = true} ≤ ENNReal.ofReal εa) :
    let D := sexec alt T f ell v₀ x A
    let Δ : ℝ := 12 * q * ((V : ℝ) + 1) ^ 2 * Real.exp (-(ε ^ 2 * ell / 16)) + εa
    let ρ : ℝ := 1 - 1 / (8 * Real.exp 1)
    let z : ℕ := ⌈Real.log q / (-Real.log ρ)⌉₊
    (∀ ω ∈ D.support,
      ω.time ≤ 4 * V + 3 ∧ (∀ i, i ∉ ω.corrupted → ω.active i = false ∧ (ω.decision i).isSome = true) ∧
        ω.msgs ≤ (4 * V + 3) * n * (n - 1)) ∧
    prob D {ω | ¬ ω.Correct x} ≤ ENNReal.ofReal (Δ + q * ρ ^ V) ∧
    expect D SCfg.time ≤ ENNReal.ofReal (3 + 4 * (z + 8 * Real.exp 1 + V * Δ)) ∧
    expect D SCfg.msgs ≤
      ENNReal.ofReal (n * ell * (7 + 4 * z + 32 * Real.exp 1 + 4 * V * Δ)) := by sorry

end BeyondDS.Supplement
