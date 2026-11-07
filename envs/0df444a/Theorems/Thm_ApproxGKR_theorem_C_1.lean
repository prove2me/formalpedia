-- Prove2me | Theorems.Thm_ApproxGKR_theorem_C_1
-- name    : ApproxGKR.theorem_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:32:13.894986+00:00
-- url     : https://prove2.me/theorems/d1aae34d-07e3-45af-a2c0-4a858014bb76
-- title:
--   Theorem C.1 (Approximate GKR) — a public-coin interactive proof that $y\approx C(x)$ for layered circuits over $\mathbb C$
-- statement:
--   There are one verifier program $V$ and one honest-prover program $P$ of the online log-cost oracle RAM, a number of rounds $R$, a coin length $\ell$ and a threshold $\Delta_0$ depending only on the public parameters $(L,(m_i),t,\delta,B_V,B_W,\Delta,\varepsilon)$, a working bit length $b$ and a constant $c$, such that the following holds for every layered arithmetic circuit $C$ over $\mathbb C$, every admissible extensions $\widetilde{\mathrm{add}}_i,\widetilde{\mathrm{mult}}_i$ (individual degree at most $\delta$, agreement with the wiring predicates on the grid, $\|\cdot\|_1\le B_W$), every input $x$ (distinct valid labels) whose exact gate values all have modulus at most $B_V$ (with $B_V,B_W\ge1$), every claim $y=(A+iB)2^{-p}$ and every rationals $\Delta>0$, $0<\varepsilon<1$:
--   1. $0<\Delta_0\le1$ and $\Delta_0<\Delta$;
--   2. $b_{\mathrm{in}}\le b\le c\beta^c$, $\ell\le c(1+\log_2((kD+L)/\varepsilon))$ and $R\le c(k+L)$;
--   3. **perfect completeness**: if $|y-C(x)|\le\Delta_0$, then for every valid oracle answers of the prover and of the verifier and for every coin tuple, $V$ accepts the honest transcript;
--   4. **soundness**: if $|y-C(x)|>\Delta$, then every adaptive prover is accepted with probability at most $\varepsilon$ over the uniform coins in $\Omega_N$, $N=2^\ell$, for every valid oracle answers;
--   5. **queries**: on every run, $V$ queries $\widetilde{\mathrm{add}}_i$ at most once and $\widetilde{\mathrm{mult}}_i$ at most once per layer $i<L$, and nothing else;
--   6. **communication**: the honest messages and the $R$ coins of $\ell$ bits total at most $c(kDb+(k+L)\ell)$ bits;
--   7. **verifier cost**: on every run (any messages, coins and valid oracle answers) $V$ halts within time $c(nmh+kD+Lmh)(b+\ell)^c$ and space $c(Db+m\ell)$;
--   8. **prover cost**: the honest prover's total time is at most $c(S+D+b+\ell)^c$.
--
--   The protocol is public coin by construction: the verifier's messages are its uniform coins, and its decision is a deterministic function of the instance, the transcript and the oracle answers. Oracle evaluations of the wiring extensions are charged only the sizes of the query and the answer.
--
--   This is the paper's approximate GKR protocol: a verifier that never repeats the circuit computation certifies, in finite precision, that a claimed output is close to the exact output of a circuit over $\mathbb C$.
--
--   Differences from the source:
--   - generalization: for the fixed circuit and extensions, "the protocol admits choices of N, 0 < ∆0 ≤ 1, and finite precision" → one verifier program, one prover program and functions R, ℓ, ∆₀, b, c chosen before the circuit, uniform over all circuits, extensions, inputs and claims; reason: the uniform statement specializes to each circuit; the paper's verifier reads only the public parameters, the oracle and the inputs
--   - reading: "running times count bit operations"; "O(Db + mℓ) space"; no machine named → the online log-cost oracle RAM with phases (instance, current message and current coin readable; memory counted); reason: online access is the stronger reading of the space bound: the paper's accounting (p.39) does not store the transcript
--   - reading: "If b bounds the input, message, and working bit lengths and ℓ = log N" → b exposed with b_in ≤ b ≤ c·β^c, ℓ ≤ c(1 + log₂((kD + L)/ε)), R ≤ c(k + L), the same b and ℓ in every cost clause; reason: without the bounds a protocol could choose b ≥ S and evaluate the circuit inside poly(b + ℓ); the bounds are the paper's own analysis (pp.35, 39–40)
--   - reading: "The verifier queries add~i and mult~i once each per layer" → at most one query of each type per layer i < L on every run, and no other query; reason: a run that rejects early stops querying
--   - reading: "evaluates the input extension twice at the end" → carried by the n·m·h term of the verifier's time bound; reason: a description of the verifier's work, not a separate property of an existential protocol
--   - generalization: "accepted with probability one" → accepted on every coin tuple; reason: implies probability one
--   - generalization: "both parties may query these polynomials … to any requested absolute error" → completeness and soundness for every oracle answer function within the requested error (adversarial), for the prover and the verifier separately; reason: covers every way the requested accuracy is met
--   - reading: Theorem C.1's "0 < ∆0 ≤ 1" → also ∆₀ < ∆; reason: Theorem 2.1 (p.6), the informal version, states 0 < ∆0 < ∆; (C.18) gives it
--   - encoding: "every prover" → every deterministic adaptive prover (message t a function of the coins before t); reason: a randomized prover is a mixture of deterministic ones and the bound passes to mixtures
--   - encoding: O(·) and poly(·) bounds → one explicit constant c used as factor and exponent; reason: the same content
--   - encoding: the n input gates at known labels; y, ∆, ε, the inputs as numbers → an input list with distinct valid labels; Gaussian dyadics and rationals in a self-delimiting binary encoding; reason: the paper's instance; the bit sizes define b_in
-- source:
--   Das, Gupta, Mondal, More, Delegating Computation with Approximate Arithmetic: Interactive Proofs for Wizards (manuscript, sha256 78b2a36b…), Theorem C.1, pp.33–34; Theorem 2.1, p.6; App. B.2, p.27

import Mathlib
import Definitions.Def_ApproxGKR_dyadicVal
import Definitions.Def_ApproxGKR_LayeredCircuit
import Definitions.Def_ApproxGKR_RAMRun
import Definitions.Def_ApproxGKR_Instance

namespace ApproxGKR

/-- **Theorem C.1 (Approximate GKR)** (pp.33–34).

Das, Gupta, Mondal, More, *Delegating Computation with Approximate Arithmetic* (manuscript,
sha256 78b2a36b…), Theorem C.1, pp.33–34: "Fix the circuit and the polynomial extensions `add~i`,
`mult~i` of the wiring predicates above, with the stated bounds on gate values and coefficients,
and let `y = (A + iB)2^{−p}` … For rational parameters `∆ > 0` and `0 < ε < 1`, the protocol admits
choices of `N`, `0 < ∆0 ≤ 1`, and finite precision such that an honest prover is accepted with
probability one whenever `|y − C(x)| ≤ ∆0`, while every prover is accepted with probability at
most `ε` whenever `|y − C(x)| > ∆`. The protocol is public coin. The verifier queries `add~i` and
`mult~i` once each per layer and evaluates the input extension twice at the end. If `b` bounds the
input, message, and working bit lengths and `ℓ = log N`, communication is `O(kDb + (k + L)ℓ)`.
With the costs of evaluating the polynomial extensions `add~i`, `mult~i` of the wiring predicates
charged separately, the honest prover takes `poly(S, D, b + ℓ)` time, and the verifier takes
`O(nmh + kD + Lmh) poly(b + ℓ)` time and `O(Db + mℓ)` space."

There are one verifier program `V`, one honest-prover program `P`, a number of rounds `R`, a coin
length `ℓ` and a threshold `∆₀` depending only on the public parameters
`(L, (mᵢ), t, δ, B_V, B_W, ∆, ε)`, a bit-length bound `b` and a constant `c` such that for every
layered circuit, every admissible extensions, every input with gate values bounded by `B_V`,
every claim `y`, every rational `∆ > 0` and `0 < ε < 1`, with `q` the instance:
1. `0 < ∆₀ ≤ 1` and `∆₀ < ∆`;
2. `b_in ≤ b ≤ c·β^c`, `ℓ ≤ c(1 + log₂((kD + L)/ε))`, `R ≤ c(k + L)`;
3. (perfect completeness) if `|y − C(x)| ≤ ∆₀`, the verifier accepts the honest transcript for
   every coin tuple and every valid oracle answers of both parties;
4. (soundness) if `|y − C(x)| > ∆`, every adaptive prover is accepted with probability at most `ε`,
   for every valid oracle answers;
5. (queries) on every run, at most one query to `add~ᵢ` and one to `mult~ᵢ` per layer `i < L`;
6. (communication) honest message bits plus `R·ℓ` coin bits are at most `c(kDb + (k + L)ℓ)`;
7. (verifier) on every run, time `≤ c(nmh + kD + Lmh)(b + ℓ)^c` and space `≤ c(Db + mℓ)`;
8. (prover) the honest prover's total time is at most `c(S + D + b + ℓ)^c`.

**Formalization Note**
* The machine is the online log-cost oracle RAM of `RAMRun`; the verifier runs `R` phases with
  read access to the instance, the current message and the current coin only. Public coin is
  built in: the verifier's messages are the uniform coins in `Fin 2^ℓ`, and its decision is a
  deterministic function of the instance, the transcript and the oracle answers.
* Oracle answers are adversarial within the requested error (`OracleValid`); an oracle call
  costs the sizes of the query and the answer ("charged separately").
* `b` and `ℓ` are exposed and bounded (`b_in ≤ b ≤ c·β^c`), so that a large "working precision"
  cannot pay for evaluating the circuit; `β = betaSize q`.
* Malicious provers are deterministic functions of the earlier coins (a randomized prover is a
  mixture of these).
* The verifier's two evaluations of the input extension are part of its work and are paid for by
  the `nmh` term of item 7. -/
theorem theorem_C_1 :
    ∃ (V P : Program) (R ℓ : Params → ℕ) (Δ₀ : Params → ℚ) (b : Instance → ℕ) (c : ℕ),
      ∀ (C : LayeredCircuit) (δ BV BW : ℕ) (ext : ExtFamily C) (x : InputList)
        (y : GaussDyadic) (Δ ε : ℚ),
        1 ≤ BV → 1 ≤ BW → (∀ i < C.L, ∀ ty, IsAdmissibleExt C δ BW i ty (ext i ty)) →
        ValidInputs C x → GateBound C x BV → 0 < Δ → 0 < ε → ε < 1 →
        let q := mkInstance C δ BV BW Δ ε y x
        let pr := q.params
        (0 < Δ₀ pr ∧ Δ₀ pr ≤ 1 ∧ Δ₀ pr < Δ) ∧
        (binSize q ≤ b q ∧ b q ≤ c * betaSize q ^ c ∧
          (ℓ pr : ℝ) ≤ c * (1 + Real.logb 2 (((pr.k * pr.D + pr.L : ℕ) : ℝ) / (ε : ℝ))) ∧
          R pr ≤ c * (pr.k + pr.L)) ∧
        (‖dyadicVal y - output C x‖ ≤ ((Δ₀ pr : ℚ) : ℝ) →
          ∀ OP OV : OracleAnswers, OracleValid C ext OP → OracleValid C ext OV →
          ∀ (coin : Fin (R pr) → Fin (2 ^ ℓ pr)) (msg : ℕ → List Bool),
            IsHonestTranscript P C q (R pr) (ℓ pr) coin OP msg →
              Accepts V q (R pr) (ℓ pr) msg coin OV) ∧
        (((Δ : ℚ) : ℝ) < ‖dyadicVal y - output C x‖ →
          ∀ (Pstar : ℕ → List ℕ → List Bool) (OV : OracleAnswers), OracleValid C ext OV →
            acceptProb V q (R pr) (ℓ pr) Pstar OV ≤ ((ε : ℚ) : ℝ)) ∧
        (∀ (msg : ℕ → List Bool) (coin : Fin (R pr) → Fin (2 ^ ℓ pr)) (OV : OracleAnswers),
          OracleValid C ext OV →
          ∃ o : Outcome, RAMRun V q.encode (R pr) msg (coinSeq coin) OV o ∧
            QueriesOK C.L o.queries ∧
            o.time ≤ c * (x.length * pr.mMax * pr.h + pr.k * pr.D + pr.L * pr.mMax * pr.h) *
              (b q + ℓ pr) ^ c ∧
            o.space ≤ c * (pr.D * b q + pr.mMax * ℓ pr)) ∧
        (∀ (coin : Fin (R pr) → Fin (2 ^ ℓ pr)) (OP : OracleAnswers), OracleValid C ext OP →
          ∃ (msg : ℕ → List Bool) (tm : ℕ → ℕ),
            (∀ t, 1 ≤ t → t ≤ R pr → ∃ space,
              SRun P (proverInput C q t (coinsBefore coin t)) OP (msg t) (tm t) space) ∧
            (∑ t ∈ Finset.Icc 1 (R pr), (msg t).length) + R pr * ℓ pr ≤
              c * (pr.k * pr.D * b q + (pr.k + pr.L) * ℓ pr) ∧
            ∑ t ∈ Finset.Icc 1 (R pr), tm t ≤ c * (C.size + pr.D + b q + ℓ pr) ^ c) := by sorry

end ApproxGKR
