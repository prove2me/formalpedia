-- Prove2me | Theorems.Thm_BeyondDS_Supplement_theorem_2
-- name    : BeyondDS.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T05:10:52.527914+00:00
-- url     : https://prove2.me/theorems/f6b7a00d-bb5c-4b41-a734-f9fc33b9a0ef
-- title:
--   Theorem 2 — static broadcast with public collectors: error $e^{-\Omega(\lambda)}+\mathrm{negl}(\kappa)$, $O(1)$ rounds, $O(n\lambda)$ messages, and the linear dependence on $n$ is optimal
-- statement:
--   Let $n=2t+1$, with binary inputs and a late common election, and suppose the corrupt set is fixed before fresh public collector samples are revealed.
--
--   **Upper bound.** There are absolute constants $c,C_1,C_2>0$, one protocol $\Pi$ on bit strings with a public collector-sample schedule, and a polynomial $p$, such that $\Pi$ is efficient and the following hold in the static-corruption model with the ideal uniform election.
--
--   1. For every perfectly correct signature scheme, all $\kappa$ and $t$, every $\lambda\ge1$, every sender, input bit and adversary, with $\epsilon$ the probability of a forgery in this execution:
--   $$\Pr[\text{broadcast fails}]\le e^{-c\lambda}+\epsilon,\qquad \mathbb E[M]\le C_1\,(n\lambda+n\lambda^2\epsilon),\qquad \mathbb E[T]\le C_2\,(1+\lambda\epsilon).$$
--   2. For every efficient, perfectly correct scheme family that is unforgeable under chosen-message attacks, all polynomially bounded $t_\kappa,\lambda_\kappa$ with $\lambda_\kappa\ge1$, every sender and input, and every non-uniform probabilistic polynomial-time adversary family, there is a negligible $\nu$ with
--   $$\Pr[\text{broadcast fails}]\le e^{-c\lambda_\kappa}+\nu(\kappa),\qquad \mathbb E[M]\le C_1\,n_\kappa\lambda_\kappa+\nu(\kappa),\qquad \mathbb E[T]\le C_2+\nu(\kappa).$$
--
--   Here $M$ counts every message sent while its sender is honest, through halting, and $T$ is the number of rounds until every currently honest player has halted.
--
--   **Optimality in $n$.** For every $n\ge2$, every protocol with arbitrary input-independent setup and arbitrary batching, every fixed delivery schedule, every designated sender and every $\eta$: if Byzantine broadcast succeeds with probability at least $1-\eta$ in the fault-free execution with sender input $0$ and in the one with sender input $1$, then in one of these two executions the expected number of messages is at least
--   $$\frac{(1-2\eta)(n-1)}{2}.$$
--
--   The upper bound is linear in $n$ for each fixed $\lambda$, and the lower bound shows that no broadcast protocol with error bounded below $1/2$ does better than linear.
--
--   **Formalization Note** The model is `execStatic`: the collector samples are uniform identities revealed at the boundaries named by the protocol's public schedule, uncounted and taking no extra round, and the corrupt set is frozen from the first reveal on. The lower bound is stated for `LocalProtocol`. Expectations are in $[0,\infty]$ and the bounds hold for every adversary, so the supremum is outside the expectation.
--
--   Differences from the source:
--   - reading: "the same framework has error exp(−Ω(λ)) + negl(κ), expected O(1) rounds, and expected O(nλ) messages, up to negligible additive terms" → ∃ absolute constants c, C₁, C₂ > 0 and one efficient protocol with a public sample schedule satisfying the bounds for all parameters with λ ≥ 1; reason: Ω and O hide absolute constants and "the same framework" names no fixed parameter choice; the statement is existential in the protocol, as the published goal is
--   - generalization: bounds up to negligible additive terms, for unforgeable signatures → also the bounds e^{−cλ} + ϵ, C₁(nλ + nλ²ϵ), C₂(1 + λϵ) for every scheme and every adversary, with ϵ the execution's forgery probability; reason: this is the explicit form of Corollary 6.2, of which the negl(κ) clause is the cryptographic case; both are stated
--   - generalization: the corrupt set is fixed before fresh public collector samples → the adversary may corrupt adaptively until the first sample reveal and never afterwards; reason: every corrupt set fixed in advance is such an adversary
--   - reading: "its dependence on n is optimal" → Proposition 6.3's lower bound (1 − 2η)(n − 1)/2 on the expected messages of any broadcast protocol; reason: Proposition 6.3 is the statement the paper proves for this sentence
--   - generalization: Proposition 6.3 assumes error at most η against every adversary, and common randomness released on a fixed public schedule → success probability ≥ 1 − η is assumed only in the two fault-free executions; any fixed delivery schedule; common randomness is part of the setup sample; reason: the proof uses only the two fault-free executions; a protocol reading common randomness on a schedule is a protocol that holds it from the start
--   - encoding: λ a real statistical parameter; expectations of M and T → λ a natural number; expectations in [0, ∞]; collector samples delivered with the boundary from a pseudo-identity; reason: conventions of the base mission; same instances
-- source:
--   Rambaud, Beyond Dolev–Strong: Adaptive Byzantine Broadcast with Õ(n^{3/2}) Messages at a Tight Honest Majority, STOC 2027 submission (manuscript sha256 c84cf9c9…), Theorem 2, p.3 (PDF p.4); Corollary 6.2, pp.20–21 (PDF pp.21–22), eqs. (7)–(9); Proposition 6.3, p.21 (PDF p.22); §6.1, pp.19–20 (PDF pp.20–21)

import Mathlib
import Definitions.Def_BeyondDS_Supplement_execStatic
import Definitions.Def_BeyondDS_Supplement_LocalProtocol

set_option autoImplicit false

open QAlgorithms.Complexity
open MeasureTheory
open scoped ENNReal
open Polynomial

namespace BeyondDS.Supplement

open BeyondDS

/-- Theorem 2 (Static broadcast), Rambaud, *Beyond Dolev–Strong*, STOC 2027 submission (manuscript sha256 c84cf9c9…), p.3 (PDF 4): "For λ ≥ 1, if the corrupt set is fixed before fresh public collector samples, the same framework has error exp(−Ω(λ)) + negl(κ), expected O(1) rounds, and expected O(nλ) messages, up to negligible additive terms. For fixed λ, this is linear in n, and its dependence on n is optimal." Explicit form: Corollary 6.2, pp.20–21 (PDF 21–22), eqs. (7)–(9); optimality: Proposition 6.3, p.21 (PDF 22).

Part 1 (upper bound). There are absolute constants `c, C₁, C₂ > 0`, one protocol `Pi` and one public collector-sample schedule `sched`, efficient in the sense of `IsEfficientStaticProtocol`, such that:

1. for every perfectly correct scheme `S`, all `κ, t` and every `λ ≥ 1`, every sender, input bit and adversary (computationally unbounded included), in the static-corruption model `execStatic` with the ideal uniform election, writing `ε` for the forgery probability of this very execution: the broadcast error is at most `exp(−cλ) + ε`, `E[M] ≤ C₁(nλ + nλ²ε)` and `E[T] ≤ C₂(1 + λε)`;
2. for every efficient, perfectly correct, EUF-CMA scheme family, polynomially bounded `t_κ, λ_κ` with `λ_κ ≥ 1`, every sender and input and every non-uniform probabilistic polynomial-time adversary family: the error is at most `exp(−cλ_κ) + negl(κ)`, `E[M] ≤ C₁ n_κ λ_κ + negl(κ)` and `E[T] ≤ C₂ + negl(κ)`.

Part 2 (optimality of the dependence on `n`, Proposition 6.3). For every `n ≥ 2`, every protocol of the local model `LocalProtocol` (arbitrary input-independent setup and common randomness, arbitrary batching), every fixed delivery schedule, every sender `s` and every `η`: if Byzantine broadcast succeeds with probability at least `1 − η` in the fault-free executions with sender input `0` and with sender input `1`, then one of these two executions has expected honest point-to-point message count at least `(1 − 2η)(n − 1)/2`.

**Formalization Note.** `M` (`msgCount`) counts every message sent while its sender is honest, through halting; `T` (`roundsUsed`) counts rounds until every currently honest player has halted; expectations are in `[0, ∞]` and the bounds hold for every adversary, so the supremum is outside the expectation. The collector samples are a public resource revealed at the boundaries the protocol's public schedule names, uncounted and taking no extra round. In Part 2 the hypothesis is only required of the two fault-free executions, which are permitted executions of every protocol with error at most `η`, and the conclusion exhibits one of them. -/
theorem theorem_2 :
    (∃ c C₁ C₂ : ℝ, 0 < c ∧ 0 < C₁ ∧ 0 < C₂ ∧
      ∃ (Pi : Protocol Str Str) (sched : Params → ℕ → ℕ) (p : ℕ[X]),
        IsEfficientStaticProtocol Pi sched p ∧
        (∀ (S : Sig) (P : Params) (x : Bool) (A : Adversary P.n Str Str),
          S.Correct → 1 ≤ P.lam →
          let D := execStatic Pi sched S P x (uniformElect P) A
          let ε := prob D {ω | Forge ω}
          prob D {ω | Fail P x ω} ≤ ENNReal.ofReal (Real.exp (-(c * P.lam))) + ε ∧
          expect D msgCount ≤ ENNReal.ofReal C₁ *
            (ENNReal.ofReal ((P.n : ℝ) * P.lam) + ENNReal.ofReal ((P.n : ℝ) * (P.lam : ℝ) ^ 2) * ε) ∧
          expect D (roundsUsed Pi P) ≤ ENNReal.ofReal C₂ * (1 + ENNReal.ofReal (P.lam : ℝ) * ε)) ∧
        (∀ (Sg : ℕ → Sig) (Pf : ℕ → Params) (q : ℕ[X]) (X : ℕ → Bool) (R : ReactiveFamily),
          SigFamilyEfficient Sg → (∀ κ, (Sg κ).Correct) → EUFCMA Sg →
          (∀ κ, (Pf κ).κ = κ) → (∀ κ, (Pf κ).t + (Pf κ).lam ≤ q.eval κ) →
          (∀ κ, 1 ≤ (Pf κ).lam) → R.Valid →
          ∃ ν, Negligible ν ∧ ∀ κ,
            let D := execStatic Pi sched (Sg κ) (Pf κ) (X κ) (uniformElect (Pf κ))
              (R.toAdversary κ (Pf κ).n)
            prob D {ω | Fail (Pf κ) (X κ) ω} ≤ ENNReal.ofReal (Real.exp (-(c * (Pf κ).lam)) + ν κ) ∧
            expect D msgCount ≤ ENNReal.ofReal (C₁ * (((Pf κ).n : ℝ) * (Pf κ).lam) + ν κ) ∧
            expect D (roundsUsed Pi (Pf κ)) ≤ ENNReal.ofReal (C₂ + ν κ))) ∧
    (∀ (n : ℕ), 2 ≤ n → ∀ (Pr : LocalProtocol n (Option Bool)) (delay : ℕ → Fin n → Fin n → ℕ),
      Pr.MeasurableRun delay → ∀ (s : Fin n) (η : ℝ),
        (∀ b : Bool, ENNReal.ofReal (1 - η) ≤ Pr.μ {ω | Pr.BroadcastOK delay s b ω}) →
        ∃ b : Bool, ENNReal.ofReal ((1 - 2 * η) * ((n : ℝ) - 1) / 2) ≤
              ∫⁻ ω, Pr.numMsgs delay ∅ (bcastInput s b) ω ∂Pr.μ) := by sorry

end BeyondDS.Supplement
