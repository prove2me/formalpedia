-- Prove2me | Theorems.Thm_BeyondDS_Supplement_theorem_6
-- name    : BeyondDS.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T05:12:22.326374+00:00
-- url     : https://prove2.me/theorems/32086cb9-7924-4cac-bfd8-d557bf201ad0
-- title:
--   Theorem 6 — conditional compiler bound: error $\le q^J+\beta$ and $\mathbb E[M]\le c_A\big(\tfrac{6}{1-q}+6J\beta+3\big)+c_T+D\beta$
-- statement:
--   Consider the compiler of §5.2 with any dissemination implementation of duration $d$ and any termination procedure, using $J$ main iterations followed by two publicly scheduled forwarding calls, so $Q=6J+3$ dissemination invocations. At the end of the second forwarding call every remaining player stops, and an undecided player takes the fallback bit. Let $n=2t+1$, let the election be at statistical distance at most $\zeta$ from uniform conditional on every transcript, and fix a correct signature scheme, a sender input and an adversary.
--
--   Let $F_c$ be the declared statistical failure event of call $c$, and let $\sigma$ be the first beginning of a call at which some currently uncorrupted player holds a termination certificate whose signatures verify and are authentic (attributed to a corrupted identity, or on data that identity has signed), or the final deadline if there is none. Suppose that for constants $\delta,\epsilon,c_A,c_T\ge0$ and $D$:
--
--   1. from every reachable prefix at the beginning of a call, the call's failure event has conditional probability at most $\delta$;
--   2. from every such prefix, the expected number of honest messages of the call is at most $c_A$;
--   3. in every call that begins before $\sigma$, if its failure event does not occur and no signature has been forged, the source payload of every player honest for the whole invocation is returned to every player honest for the whole invocation;
--   4. on every history with no failure event and no forgery on which $\sigma$ is at most the first forwarding call, every forever-honest player decides from a verifying termination certificate by the final deadline;
--   5. for every prefix $h$ that ends at the boundary $\sigma$ with no earlier failure, $\mathbb E[M_\sigma\mathbf 1_{G_\sigma}\mid h]\le c_T$, where $M_\sigma$ is the honest traffic from that boundary on and $G_\sigma$ is the event of no later failure event and no forgery;
--   6. the honest traffic is at most $D$ on every history, and the probability of a forgery is at most $\epsilon$.
--
--   Put $\beta=Q\delta+\epsilon$ and $q=\tfrac12+\zeta+6\delta$, and assume $q<1$. Then
--   $$\Pr[\text{broadcast fails}]\le q^J+\beta,\qquad \mathbb E[M]\le c_A\Big(\frac{6}{1-q}+6J\beta+3\Big)+c_T+D\beta,$$
--   where $M$ is the total number of honest-sent messages, the terminal tail included.
--
--   This is the general accounting from which the static bound (Corollary 6.2) is obtained with collector dissemination.
--
--   **Formalization Note** The protocol is `compilerG`, in the execution model of the base mission. A conditional bound from a reachable prefix is a bound on the continuation law from every configuration in the support of the prefix law. Hypothesis 5 is an expectation of a product over the continuation, not an expectation conditioned on future success. The requirement that no honest player halts or omits an ordinary stage action before $\sigma$ holds by construction: only a player that has decided from a certificate consults the termination procedure.
--
--   Differences from the source:
--   - reading: "the termination procedure", invoked by a player that decides, which "permits it to halt" → a rule saying at each call beginning whether a decided player halts; until then the player performs the ordinary stage actions with its termination evidence in each payload; reason: this is the behaviour §5.2 prescribes; a procedure that replaces stage payloads "must separately prove" its safety and is not covered by the stated guarantees
--   - encoding: a dissemination implementation with fixed duration d and statistical error δ → per-round programs over the base envelopes with a pure output map, and one declared failure event F_c per call, a predicate on the configuration at the call's last boundary; reason: the envelopes carry arbitrary strings, so any message format is coded; the error event is whatever event the implementation declares
--   - reading: "Let Q ≤ 6J + 3 be an upper bound on the number of dissemination invocations" → Q = 6J + 3; reason: the protocol makes exactly 1 + 6J + 2 invocations
--   - generalization: two termination guarantees: a certificate reaches all remaining honest players before the first honest halt on successful histories; and if termination evidence is obtained by the last Commit deadline, terminal dissemination and all honest halting finish by the final deadline → one hypothesis: on successful histories with σ at most the first forwarding call, every forever-honest player decides from a verifying termination certificate; reason: the two guarantees together imply it, and it is all the proof uses of them
--   - generalization: delivery for sources and recipients honest for the stated stability intervals, in every invocation; guarantees for every permitted adversary → delivery is assumed only in calls beginning before σ and only between players uncorrupted through the whole invocation; all hypotheses concern the execution with the one given adversary; reason: the stability intervals lie inside the invocation, and the proof uses delivery only before σ and argues inside one execution
--   - encoding: ϵ, δ, c_A, c_T are bounds → real numbers assumed nonnegative; probabilities and expectations in [0, ∞]; D a natural number; reason: a bound on a probability or an expected count is nonnegative; same instances
--   - reading: "some currently uncorrupted player holds a termination certificate" → the player's verified store and the returned records that verify and are authentic at that boundary (signer corrupted, or the data signed by the signer) contain a verifying termination certificate; reason: the holder verifies returned records only in its next activation, which a corruption can pre-empt, so a forged certificate could otherwise be held with no authentication failure recorded; on histories without an authentication failure the boundary is the same
--   - reading: the model of §5.1 with any dissemination implementation meeting the interface → the execution model of the base mission (adaptive adversary, common election oracle, perfectly correct signature scheme), with implementations that are programs of that model with a bounded number of operations per sending interval; reason: §5.1 names no resource beyond signatures and the election oracle; an implementation that needs further public setup randomness, as the collector samples of §6, is used by Corollary 6.2 and is not an instance of this statement
-- source:
--   Rambaud, Beyond Dolev–Strong: Adaptive Byzantine Broadcast with Õ(n^{3/2}) Messages at a Tight Honest Majority, STOC 2027 submission (manuscript sha256 c84cf9c9…), Theorem 6, pp.18–19 (PDF pp.19–20), eq. (5); §5.1, p.14 (PDF p.15); the termination guarantees, p.18 (PDF p.19)

import Mathlib
import Definitions.Def_BeyondDS_Supplement_callTraj

set_option autoImplicit false

open QAlgorithms.Complexity
open scoped ENNReal

namespace BeyondDS.Supplement

open BeyondDS

/-- Theorem 6 (Conditional compiler bound), Rambaud, *Beyond Dolev–Strong*, STOC 2027 submission (manuscript sha256 c84cf9c9…), pp.18–19 (PDF 19–20): "Use at most J main iterations followed by two publicly scheduled forwarding calls. At the end of the second forwarding call, force every remaining player to stop, assigning a fixed fallback bit to an undecided player. This public final deadline overrides any remaining local grace period. Let Q ≤ 6J + 3 be an upper bound on the number of dissemination invocations, including the termination tail, and let ϵ bound the aggregate cryptographic failure probability. Suppose the termination procedure has the guarantees just stated and total traffic on every history is at most D. Let M denote the total number of honest-sent messages, including the terminal tail. Put β = Qδ + ϵ and q = 1/2 + ζ + 6δ < 1. Then the protocol has broadcast error at most q^J + β, and its expected honest message cost is bounded by E[M] ≤ c_A(6/(1 − q) + 6Jβ + 3) + c_T + Dβ. (5)"

The protocol is `compilerG Dis H J`: the compiler of §5.2 with an arbitrary dissemination implementation `Dis` of duration `d` (§5.1) and an arbitrary termination procedure `H`, run in the model of the base mission with an election law at statistical distance `ζ` from uniform, against an arbitrary adversary. `τ` ranges over the trajectories `[c₀, …, c_Q, ω]` of configurations at the beginnings of the `Q = 6J + 3` calls and the outcome; `F c` is the implementation's declared statistical failure event of call `c`, and `σ` is the boundary of p.18 (`sigmaG`): the first call beginning at which a currently uncorrupted player holds a termination certificate whose signatures verify and are authentic (attributed to a corrupted identity, or on data that identity has signed). The hypotheses are the guarantees of §5.1 and p.18:

1. (`hδ`) from every reachable prefix at the beginning of a call, the call's failure event has conditional probability at most `δ`;
2. (`hA`) from every such prefix, the call's expected honest traffic is at most `c_A`;
3. (`hdel`) in a call that begins before `σ`, if its failure event does not occur and no signature has been forged, every source payload is delivered between players honest for the whole invocation;
4. (`hterm`) on histories with no failure event and no forgery on which `σ` is at most the first forwarding call (termination evidence is obtained by the last Commit deadline), every forever-honest player decides from a verifying termination certificate by the public final deadline;
5. (`hT`) `E[M_σ 1_{G_σ} | h] ≤ c_T` for every prefix `h` ending at the boundary `σ` with no earlier failure, where `M_σ` is the honest traffic from that boundary on and `G_σ` the event of no later failure event and no forgery;
6. (`hD`) at most `D` honest messages on every history; (`hε`) forgery probability at most `ϵ`.

Then, with `β = Qδ + ϵ` and `q = 1/2 + ζ + 6δ < 1`, the broadcast error is at most `q^J + β` and `E[M] ≤ c_A(6/(1 − q) + 6Jβ + 3) + c_T + Dβ`.

**Formalization Note.** A conditional bound "from every reachable prefix" is a bound on the continuation law from every configuration in the support of the prefix law, since a configuration holds its whole history. "No honest player may halt or omit an ordinary stage action" before `σ` holds by construction of `compilerG`: only a player that has decided from a certificate consults `H`. A certificate counts as held at a boundary only if its records are authentic there, because the holder verifies them (and a forgery is logged) only in its next activation, which a corruption can pre-empt; on histories without an authentication failure this is the same boundary. Traffic is counted by `msgCount`, and new traffic by a truncated difference of a count that only grows. -/
theorem theorem_6 (Dis : Dissem) (hDis : Dis.WF) (H : HaltRule) (J : ℕ) (S : Sig) (hS : S.Correct)
    (P : Params) (x : Bool) (ζ : ℝ) (E : List (Event P.n CMsg CSt) → PMF (Fin P.n)) (hE : ElectNear P ζ E)
    (A : Adversary P.n CMsg CSt) (F : ℕ → Config P.n CMsg CSt A.σ → Prop)
    (δ ε cA cT : ℝ) (Dmax : ℕ) (hδ0 : 0 ≤ δ) (hε0 : 0 ≤ ε) (hA0 : 0 ≤ cA) (hT0 : 0 ≤ cT)
    (hq : 1 / 2 + ζ + 6 * δ < 1) :
    let Pi := compilerG Dis H J
    let Q : ℕ := 6 * J + 3
    let traj := (setup Pi S P x A).bind (callTraj Pi S P E A Dis.d Q)
    let Dexec := exec Pi S P x E A
    let β : ℝ := Q * δ + ε
    let q : ℝ := 1 / 2 + ζ + 6 * δ
    (∀ c, c < Q → ∀ cf ∈ (prefixLaw Pi S P x E A (Dis.d * c)).support,
      prob (runRounds Pi S P E A Dis.d cf) {cf' | F c cf'} ≤ ENNReal.ofReal δ) →
    (∀ c, c < Q → ∀ cf ∈ (prefixLaw Pi S P x E A (Dis.d * c)).support,
      expect (runRounds Pi S P E A Dis.d cf) (fun cf' => msgCount cf' - msgCount cf) ≤ ENNReal.ofReal cA) →
    (∀ τ ∈ traj.support, ∀ c, c < sigmaG Dis S P J τ → ∀ cf, τ[c + 1]? = some cf →
      ¬ F c cf → ¬ Forge cf → DeliveredG Dis S P J c cf) →
    (∀ τ ∈ traj.support, ∀ ω, τ[Q + 1]? = some ω → (∀ c, c < Q → ¬ FailAt F τ c) → ¬ Forge ω →
      sigmaG Dis S P J τ ≤ 6 * J + 1 → ∀ i, ω.ForeverHonest i → DecidedByCert Dis.d P J ω i) →
    (∀ τ ∈ traj.support, ∀ c, c < Q → sigmaG Dis S P J τ = c → (∀ c', c' < c → ¬ FailAt F τ c') →
      ∀ cf, τ[c]? = some cf → ¬ Forge cf →
      (∑' τ' : List (Config P.n CMsg CSt A.σ), callTraj Pi S P E A Dis.d (Q - c) cf τ' *
        (open Classical in
          if (∀ j, j < Q - c → ¬ FailAt (fun k => F (c + k)) τ' j) ∧
              ∀ ω, τ'[Q - c + 1]? = some ω → ¬ Forge ω then
            ((τ'[Q - c + 1]?.map fun ω => msgCount ω - msgCount cf).getD 0 : ℝ≥0∞)
          else 0)) ≤ ENNReal.ofReal cT) →
    (∀ ω ∈ Dexec.support, msgCount ω ≤ Dmax) →
    prob Dexec {ω | Forge ω} ≤ ENNReal.ofReal ε →
    prob Dexec {ω | Fail P x ω} ≤ ENNReal.ofReal (q ^ J + β) ∧
    expect Dexec msgCount ≤ ENNReal.ofReal (cA * (6 / (1 - q) + 6 * J * β + 3) + cT + Dmax * β) := by sorry

end BeyondDS.Supplement
