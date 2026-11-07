-- Prove2me | Theorems.Thm_BeyondDS_theorem_1
-- name    : BeyondDS.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:14:20.913747+00:00
-- url     : https://prove2.me/theorems/b0ecdbcd-6eb5-4a20-b165-b1b2bb1bcfe5
-- title:
--   Theorem 1 — adaptive Byzantine broadcast at $n=2t+1$ with expected $O(n\min\{n,\sqrt{n\lambda}\})$ messages and $O(1)$ rounds
-- statement:
--   There are absolute constants $C,c,C_1,C_2>0$, a polynomial $p$ and **one protocol** $\Pi$ on bit strings, generic in the signature scheme, such that:
--
--   1. **Efficiency.** $\Pi$ is efficient with polynomial $p$: one polynomial-time machine for all parameters, caps polynomial in $\kappa+t+\lambda$, and honest states and messages of polynomial length.
--   2. **Explicit bounds.** For every perfectly correct scheme $\Sigma$, all $\kappa,t,\lambda$ with $n=2t+1$ and $\lambda\ge C\log(n+1)$, every sender, input bit $x$ and adversary $A$ (computationally unbounded included), under the ideal late election, with $\epsilon$ the forgery probability in this execution:
--   $$\Pr[\text{broadcast failure}]\le e^{-c\lambda}+\epsilon,\quad \mathbb E[M]\le C_1\big(n\min\{n,\sqrt{n\lambda}\}+\lambda n^2\epsilon\big),\quad \mathbb E[T]\le C_2(1+\lambda\epsilon).$$
--   3. **Computational bounds.** For every efficient, perfectly correct, EUF-CMA secure scheme family, all parameter families with $t_\kappa+\lambda_\kappa$ polynomially bounded and $\lambda_\kappa\ge C\log(n_\kappa+1)$, all senders and inputs, and every non-uniform PPT adversary family, there is a negligible $\nu$ with
--   $$\Pr[\text{failure}]\le e^{-c\lambda_\kappa}+\nu(\kappa),\quad \mathbb E[M]\le C_1n_\kappa\min\{n_\kappa,\sqrt{n_\kappa\lambda_\kappa}\}+\nu(\kappa),\quad \mathbb E[T]\le C_2+\nu(\kappa).$$
--
--   The model: synchronous point-to-point channels; the adversary sees every transmission, schedules honest senders, interrupts a sender between sends, corrupts at most $t$ players adaptively and permanently, and cannot remove a message already sent; a fresh destination is private until its transmission is committed; the common election reveals an independent uniform identity at public round boundaries after the round's sends, and its cost is not counted. $M$ and $T$ count through halting, and the supremum over adversaries and inputs is outside the expectation.
--
--   This is the main result of the paper: Byzantine broadcast at the tight honest majority $n=2t+1$ against adaptive corruptions with subquadratic communication when $\lambda=o(n)$.
--
--   **Formalization Note** "Suffice" is an existential over one protocol; the statement does not mention the paper's compiler, which is the intended witness (Theorem 8).
--
--   Differences from the source:
--
--   - reading: "ordinary unforgeable signatures … suffice" → ∃ one protocol, uniform in all parameters and generic in the scheme, with an efficiency clause; reason: §4.2 requires polynomially bounded algorithms and executions, and a protocol per parameter would make efficiency vacuous
--   - generalization: the theorem's negl(κ) bounds → also the explicit bounds in terms of the forgery probability ϵ for every correct scheme and every adversary; reason: Theorem 8's form (33) with J = O(λ); with §4.2 it gives the negl(κ) form, which is the third clause
--   - reading: "ordinary unforgeable signatures" → EUF-CMA with perfect correctness against non-uniform PPT forgers, with honestly generated keys and non-uniform PPT adversaries; reason: p.22, "no strong-unforgeability assumption is needed"; p.12, "authenticated public verification keys"; non-uniformity on both sides composes with arbitrary parameter families
--   - reading: authentication failure → a verification of a signature of a currently uncorrupted identity on data it has not yet signed; reason: the authentication event of p.12 at the time of verification, the event EUF-CMA controls
--   - reading: "a late independent common election" → a fresh uniform identity revealed to all at public round boundaries after every send of that round; reason: p.13, "only after the iteration's proposal deadline"; p.14, "Conditional on the preceding transcript, this index is uniform"
--   - reading: the model of §§4.1, 5.1, 7.1 → atomic activations up to and including the next send, adversarial scheduling, budget rule and injection through corrupted identities; reason: "Corruption may interrupt individual send sequences, but cannot remove a message already sent"
--   - encoding: λ real → λ ∈ ℕ; reason: λ ≥ C log(n + 1) ≥ C log 2 changes by at most a constant factor under rounding
--   - encoding: t ≥ 1 for the nontrivial results → every t ∈ ℕ, including t = 0; reason: "a sole player decides locally" (p.11), and n = 1 meets every bound
--   - encoding: exp(−Ω(λ)), O(·), "a sufficiently large absolute constant C" → ∃ absolute constants C, c, C₁, C₂ > 0 before the protocol and all other quantifiers; reason: the meaning of the notation; expectations are in [0, ∞]
-- source:
--   Rambaud, Beyond Dolev–Strong: Adaptive Byzantine Broadcast with Õ(n^{3/2}) Messages at a Tight Honest Majority, STOC 2027 submission (manuscript sha256 c84cf9c9…), Theorem 1, p.3 (PDF p.4), with the preamble of §1.1, p.3

import Mathlib
import Definitions.Def_BeyondDS_EUFCMA

set_option autoImplicit false

open QAlgorithms.Complexity
open scoped ENNReal
open Polynomial

namespace BeyondDS

/-- Theorem 1 (Adaptive broadcast), Rambaud, *Beyond Dolev–Strong*, STOC 2027 submission (manuscript sha256 c84cf9c9…), p.3 (PDF 4): "For n = 2t + 1, ordinary unforgeable signatures and a late independent common election suffice for Byzantine broadcast against t adaptive corruptions, with error exp(−Ω(λ)) + negl(κ), expected O(1) rounds, and expected O(n min{n, √(nλ)}) messages, up to negligible additive terms, for λ ≥ C log(n + 1) and a sufficiently large absolute
constant C. Corruption may interrupt individual send sequences, but cannot remove a message already sent."

There are absolute constants and one protocol `Pi`, a single polynomial-time state machine for all parameters and generic in the signature scheme, such that:

1. `Pi` is efficient in the sense of `IsEfficientProtocol`.
2. For every perfectly correct scheme `S`, all `κ, t, λ` with `λ ≥ C log(n + 1)`, every sender, input bit and adversary, computationally unbounded included, writing `ε` for the forgery probability in this very execution: the error is at most `exp(−cλ) + ε`, `E[M] ≤ C₁(n min{n, √(nλ)} + λn²ε)`, and `E[T] ≤ C₂(1 + λε)`.
3. For every efficient, perfectly correct scheme family unforgeable under chosen-message attacks, polynomially bounded `t_κ, λ_κ` with `λ_κ ≥ C log(n_κ + 1)`, every sender and input, and every non-uniform probabilistic polynomial-time adversary family: the error is at most `exp(−cλ_κ) + negl(κ)`, and `E[M] ≤ C₁ n_κ min{n_κ, √(n_κ λ_κ)} + negl(κ)`, `E[T] ≤ C₂ + negl(κ)`.

The election is the ideal oracle: a fresh uniform identity is revealed to everyone at public round boundaries, after that round's sends, and its implementation cost is not counted.

**Formalization Note.** The model is `BeyondDS.exec`: atomic activations up to and including the next send (a destination is private until committed, and a sender can be interrupted between sends); the adversary sees everything transmitted, schedules honest senders, corrupts at most `t` players adaptively and permanently and acts after seeing each transmission; a sent message cannot be removed. `M`, `T` count through halting
and the supremum over adversaries is outside the expectation, as the bounds are `∀ A`. Expectations are in `[0, ∞]`, unconditional. "Suffice" is `∃ Pi`; the statement does not mention the compiler of the paper. -/
theorem theorem_1 :
    ∃ C c C₁ C₂ : ℝ, 0 < C ∧ 0 < c ∧ 0 < C₁ ∧ 0 < C₂ ∧
      ∃ (Pi : Protocol Str Str) (p : ℕ[X]),
        IsEfficientProtocol Pi p ∧
        (∀ (S : Sig) (P : Params) (x : Bool) (A : Adversary P.n Str Str),
          S.Correct → C * Real.log ((P.n : ℝ) + 1) ≤ P.lam →
          let D := exec Pi S P x (uniformElect P) A
          let ε := prob D {ω | Forge ω}
          prob D {ω | Fail P x ω} ≤ ENNReal.ofReal (Real.exp (-(c * P.lam))) + ε ∧
          expect D msgCount ≤ ENNReal.ofReal C₁ *
            (ENNReal.ofReal (P.n * min (P.n : ℝ) (Real.sqrt ((P.n : ℝ) * P.lam))) +
              ENNReal.ofReal ((P.lam : ℝ) * (P.n : ℝ) ^ 2) * ε) ∧
          expect D (roundsUsed Pi P) ≤ ENNReal.ofReal C₂ * (1 + ENNReal.ofReal (P.lam : ℝ) * ε)) ∧
        (∀ (Sg : ℕ → Sig) (Pf : ℕ → Params) (q : ℕ[X]) (X : ℕ → Bool) (R : ReactiveFamily),
          SigFamilyEfficient Sg → (∀ κ, (Sg κ).Correct) → EUFCMA Sg →
          (∀ κ, (Pf κ).κ = κ) → (∀ κ, (Pf κ).t + (Pf κ).lam ≤ q.eval κ) →
          (∀ κ, C * Real.log (((Pf κ).n : ℝ) + 1) ≤ (Pf κ).lam) → R.Valid →
          ∃ ν, Negligible ν ∧ ∀ κ,
            let D := exec Pi (Sg κ) (Pf κ) (X κ) (uniformElect (Pf κ)) (R.toAdversary κ (Pf κ).n)
            prob D {ω | Fail (Pf κ) (X κ) ω} ≤ ENNReal.ofReal (Real.exp (-(c * (Pf κ).lam)) + ν κ) ∧
            expect D msgCount ≤ ENNReal.ofReal
              (C₁ * ((Pf κ).n * min ((Pf κ).n : ℝ) (Real.sqrt (((Pf κ).n : ℝ) * (Pf κ).lam))) + ν κ) ∧
            expect D (roundsUsed Pi (Pf κ)) ≤ ENNReal.ofReal (C₂ + ν κ)) := by sorry

end BeyondDS
