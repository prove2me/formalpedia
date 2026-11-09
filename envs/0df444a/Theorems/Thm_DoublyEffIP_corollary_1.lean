-- Prove2me | Theorems.Thm_DoublyEffIP_corollary_1
-- name    : DoublyEffIP.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:19:13.053122+00:00
-- url     : https://prove2.me/theorems/6790746e-a114-4bcb-89cc-09f6452b4937
-- title:
--   Corollary 1 — languages in polynomial space and time $n^{O(\log n)}$ have IPs with $\mathrm{poly}(T)$-time provers and $\mathrm{poly}(n,\sigma)$-time verifiers
-- statement:
--   Let $T,S:\mathbb N\to\mathbb N$ with $n<T(n)\le n^{O(\log n)}$ and $S(n)\in\mathrm{poly}(n)$, that is, for some constants $c_0$ and $c_S$ and every $n$,
--
--   $$
--   n<T(n)\le 2^{\,c_0(\log_2(n+2))^2},\qquad S(n)\le c_S\,(n+1)^{c_S},
--   $$
--
--   and let $L\in\mathrm{TISP}(T,S)$. Then there are one public-coin protocol and one constant $c$ such that, for every soundness parameter $\sigma$ and every input length $n$, the protocol is a $2^{-\sigma}$-sound $(\ell,a,\mathrm{Ptime},\mathrm{Vtime})$-IP for $L$ at length $n$ with
--
--   1. $\ell\le c\,(n+\sigma+1)^c$, i.e. $\ell=\mathrm{poly}(n,\sigma)$;
--   2. $a\le S(n)\cdot c\,(n+\sigma+1)^c$;
--   3. $\mathrm{Ptime}\le c\,(S(n)+T(n)+\sigma+1)^c$, i.e. $\mathrm{poly}(S,T,\sigma)$;
--   4. $\mathrm{Vtime}\le S(n)^2\cdot c\,(n+\sigma+1)^c$.
--
--   This is the paper's headline result (Theorem 1): every language decidable in polynomial space and time $n^{O(\log n)}$ has a doubly efficient interactive proof, with an honest prover running in time polynomial in $T$ and a verifier running in time polynomial in $n$ and $\sigma$.
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
--   - reading: ℓ = poly(n, σ), a = S · poly(n, σ), Ptime = poly(S, T, σ), Vtime = S² · poly(n, σ) → c(n+σ+1)^c, S(n)·c(n+σ+1)^c, c(S(n)+T(n)+σ+1)^c, S(n)²·c(n+σ+1)^c with one c chosen after L, T, S and before σ, n; reason: standard reading of poly(·) with an explicit constant
--   - reading: T < n^{O(log n)}; S ∈ poly(n) → ∃ c₀ ∀ n, T(n) ≤ 2^{c₀ (log₂(n+2))²}; ∃ c_S ∀ n, S(n) ≤ c_S (n+1)^{c_S}; reason: equivalent to an eventual bound n^{c log n}: finitely many n are absorbed by c₀
--   - encoding: strict T < n^{O(log n)} → ≤; reason: c₀ is existential, so the class of T is the same
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Corollary 1, Section 4, p.14

import Mathlib
import Definitions.Def_DoublyEffIP_InTISP
import Definitions.Def_DoublyEffIP_Protocol
import Definitions.Def_DoublyEffIP_IsSoundIP

set_option autoImplicit false

namespace DoublyEffIP

/-- **Corollary 1** (Formal Statement of Theorem 1) — Chen–Hong–Kalai–Xi, *Towards a Doubly
Efficient IP = PSPACE*, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 4,
p.14.

For all `T, S : ℕ → ℕ` with `n < T(n) ≤ n^{O(log n)}` and `S(n) ∈ poly(n)`, and every language
`L ∈ TISP(T, S)`, there are one protocol and one constant `c` such that for every `σ` and `n` the
protocol is a `2^{-σ}`-sound `(ℓ, a, Ptime, Vtime)`-IP for `L` at length `n`, with
* `ℓ ≤ c (n + σ + 1)^c` (`poly(n, σ)`),
* `a ≤ S(n) · c (n + σ + 1)^c`,
* `Ptime ≤ c (S(n) + T(n) + σ + 1)^c` (`poly(S, T, σ)`),
* `Vtime ≤ S(n)² · c (n + σ + 1)^c`.

**Formalization Note.** `T < n^{O(log n)}` is `T(n) ≤ 2^{c₀ (log₂(n+2))²}` for one `c₀` and all
`n` (equivalent to an eventual bound `n^{c log n}`, finitely many `n` being absorbed by `c₀`;
`≤` for the printed `<` changes nothing since `c₀` is existential). `S ∈ poly(n)` is
`S(n) ≤ c_S (n+1)^{c_S}`. Every `poly(·)` is `c (· + 1)^c` with one constant `c`, chosen after
`L`, `T`, `S` and before `σ`, `n`, so one protocol serves every soundness parameter, which
specializes to every `σ = σ(n)`. The public parameters `(n, T(n), S(n), σ)` are given to the
machines in binary; no constructibility is assumed. See `IsSoundIP` and `InTISP` for the model. -/
theorem corollary_1 (T S : ℕ → ℕ) (hT : ∀ n, n < T n)
    (hTup : ∃ c₀ : ℝ, ∀ n : ℕ, (T n : ℝ) ≤ (2 : ℝ) ^ (c₀ * Real.logb 2 ((n : ℝ) + 2) ^ 2))
    (hS : ∃ cS : ℕ, ∀ n : ℕ, S n ≤ cS * (n + 1) ^ cS) (L : Set (List Bool))
    (hL : InTISP L T S) :
    ∃ (prot : Protocol) (c : ℕ), ∀ σ n : ℕ,
      IsSoundIP prot L n (T n) (S n) σ
        ((c : ℝ) * ((n : ℝ) + (σ : ℝ) + 1) ^ c)
        ((S n : ℝ) * ((c : ℝ) * ((n : ℝ) + (σ : ℝ) + 1) ^ c))
        ((c : ℝ) * ((S n : ℝ) + (T n : ℝ) + (σ : ℝ) + 1) ^ c)
        ((S n : ℝ) ^ 2 * ((c : ℝ) * ((n : ℝ) + (σ : ℝ) + 1) ^ c)) := by sorry

end DoublyEffIP
