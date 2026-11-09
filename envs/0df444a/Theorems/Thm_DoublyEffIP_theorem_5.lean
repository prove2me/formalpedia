-- Prove2me | Theorems.Thm_DoublyEffIP_theorem_5
-- name    : DoublyEffIP.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:19:37.515091+00:00
-- url     : https://prove2.me/theorems/b2c901ab-fc72-4131-87f8-a22e692013d4
-- title:
--   Theorem 5 — a $2^{-\sigma}$-sound IP for $\mathrm{TISP}(T,S)$ with $2^{O(\sqrt{\log T})}$ overhead
-- statement:
--   Let $T,S:\mathbb N\to\mathbb N$ with $T(n)>n$ for every $n$, and let $L\in\mathrm{TISP}(T,S)$. Then there are one public-coin protocol and one constant $c$ such that, for every soundness parameter $\sigma$ and every input length $n$, the protocol is a $2^{-\sigma}$-sound $(\ell,a,\mathrm{Ptime},\mathrm{Vtime})$-IP for $L$ at length $n$, where, writing
--
--   $$
--   E=c\cdot 2^{\,c\sqrt{\log_2(T(n)+2)}}\cdot\big(\sigma+\log_2(S(n)+2)+1\big)^c ,
--   $$
--
--   1. $\ell\le E$, i.e. $\ell=2^{O(\sqrt{\log T})}\cdot\mathrm{poly}(\sigma,\log S)$;
--   2. $a\le S(n)\cdot E$;
--   3. $\mathrm{Ptime}\le c\,(S(n)+T(n)+\sigma+1)^c$, i.e. $\mathrm{poly}(S,T,\sigma)$;
--   4. $\mathrm{Vtime}\le S(n)^2\cdot E$.
--
--   No assumption is made on $S$, and none on $T$ beyond $T(n)>n$. This is the general form of the paper's doubly efficient interactive proof; Corollary 1 is its special case $T=n^{O(\log n)}$, $S=\mathrm{poly}(n)$.
--
--   **Formalization Note** The public parameters $(n,T(n),S(n),\sigma)$ are given in binary to all machines; no constructibility is assumed. Machines, space and the IP conditions are as in the definitions `InTISP` and `IsSoundIP`.
--
--   Differences from the source:
--   - reading: both parties have explicit access to the input parameters pp (unspecified) → pp = (n, T(n), S(n), σ) in self-delimited binary, given to every machine; no constructibility of T or S; reason: Section 3.4 and the proof of Theorem 5 ("Both parties select the appropriate parameters"); without pp a verifier could not know σ
--   - reading: TISP(T, S) space S(n) → visited cells of every tape, the input tape included; reason: the proof of Theorem 5 (p.15) takes the start state with x as input as a configuration in {0,1}^S
--   - reading: completeness: there exists a prover strategy P; P is deterministic and runs in time Ptime → completeness by the protocol's own prover machine, a stateless next-message machine a_j = P(x, j, q_0..q_j), whose running times over the ℓ rounds sum to at most Ptime on every input of length n, with no private auxiliary input beyond (pp, x, j, queries); reason: p.10 and p.11 ("aj := P(x, j, (q1, . . . , qj))"); otherwise Ptime would bound nothing
--   - reading: ℓ and a, numbers of the protocol → computed from pp by a parameter machine within Vtime steps; reason: the verifier must know ℓ and a; this keeps them from carrying advice
--   - generalization: σ = σ(n) ∈ N, one protocol for that function → one protocol and one constant c for all σ, with σ in pp; reason: setting σ := σ(n) at each n gives the printed statement
--   - encoding: a Turing machine; V probabilistic, interacting → published multitape PrimitiveMachine (SubexponentialSAT); V a deterministic machine run on (pp, x, queries, answers), halting within Vtime on every query and answer sequence; reason: the paper fixes no model; public coins and "V never rejects in the middle of an execution"
--   - encoding: Pr over the verifier's coins q ←R Σ^a; Pr = 1; Pr ≤ 2^{−σ} → counts over Fin ℓ → List.Vector Bool a: every q; #{q accepted} · 2^σ ≤ 2^{ℓa}; reason: the coins are uniform, so the values are the same
--   - encoding: rounds j ∈ [ℓ]; messages in Σ^a with Σ = {0,1} → 0-based round index; messages of type List.Vector Bool a; reason: same protocols
--   - encoding: any (computationally unbounded) prover strategy P* → any function from the list of queries so far to an a-bit answer, chosen after x; reason: x and pp are fixed before P* is chosen, the round index is the list's length, and a randomized strategy is a mixture of deterministic ones, so the bound is the same
--   - reading: ℓ = 2^{O(√log T)}·poly(σ, log S), a = 2^{O(√log T)}·S·poly(σ, log S), Ptime = poly(S, T, σ), Vtime = 2^{O(√log T)}·S²·poly(σ, log S) → with E = c·2^{c√(log₂(T(n)+2))}·(σ + log₂(S(n)+2) + 1)^c: ℓ ≤ E, a ≤ S(n)·E, Ptime ≤ c(S(n)+T(n)+σ+1)^c, Vtime ≤ S(n)²·E, one c chosen after L, T, S and before σ, n; reason: the constant of 2^{O(√log T)} sits inside the exponent; +2 and +1 avoid log 0 and 0^c
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Theorem 5, Section 4, p.14

import Mathlib
import Definitions.Def_DoublyEffIP_InTISP
import Definitions.Def_DoublyEffIP_Protocol
import Definitions.Def_DoublyEffIP_IsSoundIP

set_option autoImplicit false

namespace DoublyEffIP

/-- **Theorem 5** (Formal Statement of Theorem 2) — Chen–Hong–Kalai–Xi, *Towards a Doubly
Efficient IP = PSPACE*, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 4,
p.14.

For all `T, S : ℕ → ℕ` with `T(n) > n` for every `n`, and every language `L ∈ TISP(T, S)`, there
are one protocol and one constant `c` such that for every `σ` and `n`, the protocol is a
`2^{-σ}`-sound `(ℓ, a, Ptime, Vtime)`-IP for `L` at length `n`, with
`E := c · 2^{c·√(log₂(T(n)+2))} · (σ + log₂(S(n)+2) + 1)^c`:
* `ℓ ≤ E` (`2^{O(√log T)} · poly(σ, log S)`),
* `a ≤ S(n) · E`,
* `Ptime ≤ c (S(n) + T(n) + σ + 1)^c` (`poly(S, T, σ)`),
* `Vtime ≤ S(n)² · E`.

**Formalization Note.** `2^{O(√log T)} · poly(σ, log S)` is read with one constant `c`, inside the
exponent and in the polynomial; `+2` and `+1` avoid `log 0` and `0^c`. `c` is chosen after `L`,
`T`, `S` and before `σ` and `n`, so one protocol serves every soundness parameter, which
specializes to every `σ = σ(n)`. The public parameters `(n, T(n), S(n), σ)` are given to the
machines in binary; no constructibility is assumed. See `IsSoundIP` and `InTISP` for the model. -/
theorem theorem_5 (T S : ℕ → ℕ) (hT : ∀ n, n < T n) (L : Set (List Bool))
    (hL : InTISP L T S) :
    ∃ (prot : Protocol) (c : ℕ), ∀ σ n : ℕ,
      let E : ℝ := (c : ℝ) * (2 : ℝ) ^ ((c : ℝ) * Real.sqrt (Real.logb 2 ((T n : ℝ) + 2))) *
        ((σ : ℝ) + Real.logb 2 ((S n : ℝ) + 2) + 1) ^ c
      IsSoundIP prot L n (T n) (S n) σ E ((S n : ℝ) * E)
        ((c : ℝ) * ((S n : ℝ) + (T n : ℝ) + (σ : ℝ) + 1) ^ c) ((S n : ℝ) ^ 2 * E) := by sorry

end DoublyEffIP
