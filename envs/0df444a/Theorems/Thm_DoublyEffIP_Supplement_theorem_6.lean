-- Prove2me | Theorems.Thm_DoublyEffIP_Supplement_theorem_6
-- name    : DoublyEffIP.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:45:56.921356+00:00
-- url     : https://prove2.me/theorems/e58b6957-f306-4f66-b347-a8f85ea1f359
-- title:
--   Theorem 6 — LDP-IP $\mathrm{Batch}(t,k)$ for $L^k_t$ (corrected: depth bound has $\log S,\log k$)
-- statement:
--   Fix a machine $M$. There are a function $\Lambda:\mathbb N\times\mathbb N\to\mathbb N$ and a constant $C_\Lambda$ with
--
--   $$
--   \Lambda(T,k)\le 2^{\,C_\Lambda\sqrt{\log_2\binom{2\lceil\log_2 T\rceil+\lceil\log_2 k\rceil}{\lceil\log_2 T\rceil}}}\quad\text{for all }T,k,
--   $$
--
--   and there are a protocol (with a binary field chosen from its parameters), a log-space uniform generator $T_\Psi$ and a constant $c$ such that, for all $S,T,k,\sigma$ and $t\le T$, the protocol $\mathrm{Batch}(t,k)$ with public parameters $(\sigma,S,T,t,k)$ is a $2^{-\sigma}$-sound LDP-IP for the batch language $L^k_t$ of $M$ on $k$ pairs of space-$S$ configurations. Writing $\Lambda=\Lambda(T,k)$, $\mathrm{poly}(\sigma)=c(\sigma+1)^c$ and $S'=S+1$:
--
--   1. $\epsilon=2^{-\sigma}$;
--   2. $\ell\le\Lambda\cdot\mathrm{poly}(\sigma)$ and $a\le\Lambda\cdot S'\cdot\mathrm{poly}(\sigma)$;
--   3. $\mathrm{Ptime}\le c\,(T+k+S+\sigma+1)^c$;
--   4. $\mathrm{Vtime}\le\Lambda\cdot S'^2\cdot\mathrm{poly}(\sigma)$;
--   5. the implementation circuit $C_\Psi$ of every output $\langle\Psi\rangle$ has $\mathrm{size}(C_\Psi)\le(k+\Lambda)\cdot S'\cdot\mathrm{poly}(\sigma)$ and
--   $$
--   \mathrm{depth}(C_\Psi)\le\Lambda\cdot c\,\big(\sigma+\log_2\max(S,2)+\log_2\max(k,2)+1\big)^c ;
--   $$
--   6. $|\langle\Psi\rangle|\le\Lambda\cdot\mathrm{poly}(\sigma)\cdot S'$.
--
--   This batch protocol verifies $k$ claims "configuration $u$ reaches configuration $v$ in exactly $t$ steps" with a verifier whose cost grows like $\Lambda(T,k)$ rather than like $t$ or $k$; with $k=1$ it gives the doubly efficient proof of Theorem 5.
--
--   **Formalization Note** $\Lambda$ and $C_\Lambda$ are chosen after $M$, the protocol and $c$ after them. Configurations are windows of $2S+1$ cells per tape, encoded in $O(S+1)$ bits.
--
--   Differences from the source:
--   - correction: depth(C_Ψ) = Λ(T,k)·poly(σ) → depth(C_Ψ) ≤ Λ(T,k)·c(σ + log₂max(S,2) + log₂max(k,2) + 1)^c; reason: the printed bound is false: a fan-in-2 circuit of depth D reads at most 2^D input positions, so a sound LDP-IP with perfect completeness and σ = 1 needs depth ≥ log₂(k/2) (change the end of an unread row; a prover replaying the honest answers for the correct batch is accepted with probability ≥ 1 − 2^D/k), and likewise depth ≥ log₂ S − O(1); with T = n + 1 and k = 2^{2^n}, Λ(T,k)·c(σ+1)^c ≤ 2^{C√((n+2)⌈log₂(n+1)⌉)}·c·2^c < 2^n − 1 = log₂(k/2) for large n. The paper's Õ (pp.27–30) hides polylog(n, S, T, k) and drops it; the factors log S, log k are restored
--   - reading: Λ(T,k) ∈ 2^{O(√(log (2 log T + log k over log T)))} → one function Λ : ℕ → ℕ → ℕ with Λ(T,k) ≤ 2^{C_Λ √(log₂ binom(2⌈log₂T⌉ + ⌈log₂k⌉, ⌈log₂T⌉))}, Λ and C_Λ chosen right after M; reason: the stacked pair is a binomial coefficient (App. B, p.40, λ = ⌈2^{√log binom(X+Y, X)}⌉; read as a fraction, Λ(T,1) would be O(1), contradicting p.15 Λ(T,1) = 2^{O(√log T)}); ceilings change log binom by a constant factor for T ≥ 2 and nothing for T ≤ 1
--   - generalization: n ∈ N and S = S(n), T = T(n), t = t(n) ≤ T, k = k(n), σ = σ(n) ∈ N → one protocol and one constant c for all numbers S, T, t ≤ T, k, σ (pp = ⟨σ⟩⟨S⟩⟨T⟩⟨t⟩⟨k⟩); reason: setting the numbers to their values at each n gives the printed statement
--   - reading: M with time complexity T(n) and space complexity S(n); configurations x_start, x_end ∈ {0,1}^{S(n)}; L_t of M's transitions → any machine M; configurations WinCfg M S (state, and head and contents of a (2S+1)-cell window per tape) with the step clipped at the window edge, encoded injectively in winWidth M S = O(S+1) bits; L_t through the published DoublyEffIP.Lt; reason: runs of space S stay inside the window, where the step is M's own; the clip makes the step total on all S-configurations, as L_t on {0,1}^S × {0,1}^S needs; M's own time and space bounds are not used by the statement
--   - encoding: S in the bounds a, Vtime, size(C_Ψ), |⟨Ψ⟩| → S + 1; reason: a configuration has at least one bit (winWidth ≥ 1); for S ≥ 1, S + 1 ≤ 2S is absorbed in poly(σ), so only the degenerate S = 0 changes
--   - reading: an LDP-IP 'with respect to a field F'; F a binary field specified in Protocol 1 → the protocol chooses a binary field presentation from pp (part of the protocol), output by its parameter machine; Ψ's circuit is evaluated over that field with gen = the class of X; reason: Protocol 1: 'F is the smallest binary field such that …', computed from the parameters
--   - reading: poly(σ); O(·) → c(σ+1)^c with one constant c chosen after M and Λ, before S, T, t, k, σ; reason: the standard reading with one universal constant
--   - encoding: x ∈ {0,1}^{2S·k}; L^k_t → x a bit list of length k·2·winWidth M S; L^k_t = encodings of batches in the published DoublyEffIP.Lkt; strings that encode no batch are not in L^k_t; reason: Table 1 and Protocol 1
--   - encoding: a Turing machine (prover, verifier); V probabilistic → published multitape PrimitiveMachine; V a deterministic machine run on (queries, answers, pp), halting within Vtime on every query and answer sequence; reason: the paper fixes no model; public coins and 'V never rejects in the middle of an execution'
--   - encoding: uniform circuit families generated by a fixed O(f)-space Turing machine → the published TreeEdgeRankPC.Transducer (read-only input, one work tape, write-only output) with work space c·(f+1), c one constant per family; reason: the standard space-bounded transducer model; O(f) with one constant per family
--   - encoding: arithmetic circuits of fan-in 2 ADD and MULT gates; descriptions ⟨·⟩; size and depth → Circuit: gates add/mul/const 0,1/gen (field generator α), wires numbered inputs first; encCircuit; size = number of gates; depth = longest input-output path; reason: constants are needed for any non-homogeneous predicate (e.g. ⊤ outputs 1); gen gives every field constant
--   - encoding: Pr over the verifier's coins q ←R {0,1}^a; Pr = 1; Pr ≤ 2^{−σ} → counts over Fin ℓ → List.Vector Bool a: every q; #{q} · 2^σ ≤ 2^{ℓa}; reason: the coins are uniform, so the values are the same
--   - reading: completeness: there exists a prover strategy P; P is deterministic and runs in time Ptime → completeness by the protocol's own stateless next-message prover machine, whose running times over the ℓ rounds sum to at most Ptime on every input; reason: p.10 ('The machine P is deterministic and runs in time Ptime'); otherwise Ptime would bound nothing
--   - encoding: any (computationally unbounded) prover strategy P* → any function from the list of queries so far to an a-bit answer, chosen after the input; reason: the input and pp are fixed before P* is chosen; a randomized strategy is a mixture of deterministic ones
--   - reading: ℓ and a, numbers of the protocol → computed from pp by a parameter machine within Vtime steps; reason: the verifier must know ℓ and a; this keeps them from carrying advice
--   - reading: both parties have explicit access to pp (layout unspecified) → prover's word: x, round index, queries, then pp; verifier's word: queries, answers, then pp; all self-delimited; reason: the paper fixes no layout; with pp last neither party must scan parameters the time bounds do not charge for
--   - reading: the bounds on the output (|⟨Ψ⟩|, size and depth of its implementation circuit) → hold for every output ≠ ⊥ of the verifier, on every coin and answer sequence; reason: they are properties of what the verifier outputs, which it controls
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Theorem 6, Section 4.1, p.15

import Mathlib
import Definitions.Def_DoublyEffIP_Supplement_WinCfg
import Definitions.Def_DoublyEffIP_Supplement_winWidth
import Definitions.Def_DoublyEffIP_Supplement_bitBatchLang
import Definitions.Def_DoublyEffIP_Supplement_ppBatch
import Definitions.Def_DoublyEffIP_Supplement_IsLogSpaceUniform
import Definitions.Def_DoublyEffIP_Supplement_OProtocol
import Definitions.Def_DoublyEffIP_Supplement_IsSoundLDPIP
import Definitions.Def_AvgCaseTI_FieldPres
import Definitions.Def_TreeEdgeRankPC_Transducer
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT.Computation
open TreeEdgeRankPC

namespace DoublyEffIP.Supplement

/-- **Theorem 6** (LDP-IP `Batch(t, k)` for the batch language) — Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…), Section 4.1, p.15.

Fix a machine `M`. There are a function `Λ(T, k) ≤ 2^{C_Λ √(log₂ binom(2⌈log₂T⌉ + ⌈log₂k⌉,
⌈log₂T⌉))}`, a protocol with a binary field, a log-space uniform family `TΨ` and a constant `c`
such that for all `S, T, t ≤ T, k, σ` the protocol (public parameters `S, T, t, k, σ`) is a
`2^{-σ}`-sound LDP-IP for the batch language `L^k_t` of `M` on `k` pairs of space-`S`
configurations, with `poly(σ) = c(σ+1)^c` and `S' = S + 1`:
* `ℓ ≤ Λ · poly(σ)`, `a ≤ Λ · S' · poly(σ)`, `Ptime ≤ c(T+k+S+σ+1)^c`,
  `Vtime ≤ Λ · S'^2 · poly(σ)`;
* `size(C_Ψ) ≤ (k + Λ) · S' · poly(σ)`,
  `depth(C_Ψ) ≤ Λ · c(σ + log₂ max(S,2) + log₂ max(k,2) + 1)^c` (corrected);
* `|⟨Ψ⟩| ≤ Λ · poly(σ) · S'`.

**Formalization Note.** The printed `depth(C_Ψ) = Λ(T,k) · poly(σ)` is false (a sound LDP-IP for
`L^k_t` needs depth `≥ log₂(k/2)` and `≥ log₂ S − O(1)`, while `Λ` can be `2^{O(√(n log n))}` for
`k = 2^{2^n}`); the factors `log S`, `log k` are restored, as the paper's own `Õ` (pp.27–30)
hides them. `Λ` and `C_Λ` are chosen after `M`; `c` after them; `S, T, t, k, σ` are arbitrary
numbers (pointwise in the source's functions of `n`). Configurations are `WinCfg M S`, encoded by
`winEnc` in `winWidth M S = O(S+1)` bits. -/
theorem theorem_6 (M : PrimitiveMachine) :
    ∃ (Λ : ℕ → ℕ → ℕ) (CΛ : ℝ),
      (∀ T k : ℕ, (Λ T k : ℝ) ≤ (2 : ℝ) ^ (CΛ * Real.sqrt (Real.logb 2
        (((2 * Nat.clog 2 T + Nat.clog 2 k).choose (Nat.clog 2 T) : ℕ) : ℝ)))) ∧
      ∃ (prot : OProtocol) (field : List Bool → AvgCaseTI.FieldPres) (TΨ : Transducer)
        (cΨ c : ℕ),
        IsLogSpaceUniform TΨ cΨ ∧
        ∀ S T t k σ : ℕ, t ≤ T →
          let Λr : ℝ := Λ T k
          let S1 : ℝ := (S : ℝ) + 1
          let Pσ : ℝ := (c : ℝ) * ((σ : ℝ) + 1) ^ c
          IsSoundLDPIP prot field TΨ (ppBatch S T t k σ) (k * (2 * winWidth M S))
            (bitBatchLang M S t k) σ
            (Λr * Pσ)
            (Λr * S1 * Pσ)
            ((c : ℝ) * ((T : ℝ) + (k : ℝ) + (S : ℝ) + (σ : ℝ) + 1) ^ c)
            (Λr * S1 ^ 2 * Pσ)
            (((k : ℝ) + Λr) * S1 * Pσ)
            (Λr * ((c : ℝ) * ((σ : ℝ) + Real.logb 2 ((max S 2 : ℕ) : ℝ) +
              Real.logb 2 ((max k 2 : ℕ) : ℝ) + 1) ^ c))
            (Λr * Pσ * S1) := by sorry

end DoublyEffIP.Supplement
