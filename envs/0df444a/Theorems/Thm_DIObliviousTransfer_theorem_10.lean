-- Prove2me | Theorems.Thm_DIObliviousTransfer_theorem_10
-- name    : DIObliviousTransfer.theorem_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T09:13:04.942298+00:00
-- url     : https://prove2.me/theorems/93ace25b-0e7f-4848-b914-6b483ddb0155
-- title:
--   Theorem 10 — masked commit-and-prove
-- statement:
--   Assume zero-knowledge proofs as in Lemma 16 and a string commitment satisfying Definition 9. Then Protocol 5 realizes Definition 8 for adaptive sequential phases with total new-record length at most $q$ in each direction: for every honest caller, the caller with Protocol 5 substituted is indistinguishable, against either static corruption, from the caller with ideal commit-and-prove. The simulator uses only the declared device interface of the two source batches. Each direction uses one source commitment, and all later honest operations are classical and make no source or device calls.
--
--   Differences from the source:
--
--   - generalization: assume qOWFs; the commitment of Lemma 19 (BCKM on Naor) and the ZK proofs of Lemma 16 (GMW on Naor) → any bit commitment satisfying the conclusion of Lemma 19 (ComSpec) and any proof system satisfying the conclusion of Lemma 16 (ZKSpec); reason: Decision D14: the proof uses the primitives only through Lemmas 16 and 19, and under qOWFs the paper's instantiation meets both (Lemma 16 is the milestone linking ZK to qOWFs)
--   - encoding: ideal functionalities as prose interfaces; CP with Boolean-circuit predicates and an authorized predicate schedule → deterministic classical state machines with party and adversary ports; CP over a predicate language (projections and the protocol's predicates) and a schedule predicate; reason: Decision D10 (Definitions 7, 8); honest parties and in-schedule requests only use the prescribed predicates
--   - reading: nonuniform QPT adversaries, devices and simulators with polynomial-size quantum advice → families of machines whose activations are circuits of at most two-qubit unitaries and single-wire resets with classical input loaded and output measured, all sizes bounded by one polynomial in λ; advice is part of the arbitrary initial state; reason: Decision D3 (pp.2, 17): one standard reading of nonuniform QPT
--   - reading: Real ≈c Ideal, the negligible advantage bound uniform over admissible η and fixed honest inputs → for every polynomially bounded reference size and every QPT test there is one negligible ε with advantage at most ε(λ) for every λ, every admissible η and every valid honest input; reason: Decision D4 (Definition 5 (ii)); the stronger, uniform reading
--   - reading: adaptive bidirectional messages of total cost at most ℓ qubits, every adaptive control symbol charged in a self-delimiting transcript, fixed public schedule free → window steps emitting a control symbol (classical length, quantum length, next active side), scheduled or adaptive; cost = classical bits + Elias-γ encodings of adaptive control symbols + qubits; a message exceeding the remaining budget closes the window undelivered; reason: Decision D5 (Definition 3 (i)-(ii)); enforcing the budget is equivalent to quantifying over admissible strategies since both sides see the control transcript
--   - encoding: admissible initial extension η on I_H W_H K_H D_A D_B P R with classical honest input, blank workspace and fresh coins → an arbitrary density operator on (corrupt register, honest batch registers, reference); honest input, workspace and coins are classical values of the honest controller that no other component can access; reason: Decision D6 (Definition 4); same instances
--   - encoding: compared states (corrupt final cq-state, honest input/output, public transcript, R) → the cq state (honest input, honest output, transcript) ⊗ (corrupt register, R); honest batch registers and simulator scratch traced out; reason: Decision D7 (Definition 5 (i))
--   - reading: declared honest device interface Dev_H: only the prescribed classical device operations and leakage window, no reset, copy or re-preparation → the simulator may use each honest batch once, choosing its questions and playing the corrupt side of its window, and receives the answers; reason: Decision D8 (Definition 5 (iii))
--   - reading: ∃Sim after ∀P∗, receiving the corrupt workspace and devices and ideal releases, acting as Sim ⊗ id_R → the simulator is chosen after the adversary, is a QPT machine on the corrupt register plus fresh qubits, never acts on R, and outputs the transcript; reason: Decision D9 (Definition 5 (iv))
--   - encoding: composition at invocation boundaries satisfying Definition 6 in every replacement hybrid → ideal calls replaced by fresh copies of the subprotocol on fresh batches with fresh budget groups; Definition 6 holds by construction of the execution semantics; reason: Decision D11 (Definition 6, Theorem 20)
--   - encoding: all prescribed interparty messages are classical → messages have type Bits; reason: Decision D23; holds by type
--   - generalization: Boolean-circuit predicates and the protocol's authorized schedule → every polynomial-time predicate language and every polynomial-time schedule; reason: decision D10: Boolean circuits and the paper's schedule are instances
--   - reading: realizes Definition 8 for adaptive sequential phases → for every honest caller (classical controllers with polynomial resources and at most q committed bits per direction), the caller with Protocol 5 emulates the caller with ideal CP; reason: adaptive phases are chosen by the caller; this is how Theorem 18's proof uses the theorem (with caller Protocol 2)
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), Theorem 10, p.39 (PDF p.41)

import Mathlib
import Definitions.Def_DIObliviousTransfer_protocol5

namespace DIObliviousTransfer

/-- **Theorem 10 (Masked commit-and-prove)**, Batra, Chen, Jain, Zhang, arXiv:2610.01421 (held
version, sha256 8334c039…), p.39 (PDF p.41). Assume the zero-knowledge proofs of Lemma 16 and a
string commitment satisfying Definition 9. Protocol 5 realizes Definition 8 for adaptive sequential
phases with total new-record length at most `q` in each direction, with auxiliary-input-uniform
QPT simulation for either static corruption, retaining aborts and the complete continuing state.
Each direction uses one source commitment; all later honest operations are classical and make no
source or device calls.

**Formalization Note** (decisions D10, D11, D14). "Assume qOWFs" is replaced by the ZK interface
(`ZKSpec`, which Lemma 16 derives from qOWFs). Realization of Definition 8 "for adaptive sequential
phases" is stated for every honest caller (a pair of classical controllers issuing commit-and-prove
commands and waiting for deliveries, with polynomial resources and at most `q` committed bits per
direction on every branch): the caller with Protocol 5 substituted is indistinguishable from the
caller with ideal CP, the simulator having the declared device interface of the two source batches
only; the caller's own device batches are untouched (Definition 11). The predicate language and
the schedule are arbitrary polynomial-time ones (a generalization of Boolean circuits and of the
paper's fixed schedule). The source's windows keep the budgets for which Definition 9 holds; the
caller's windows have arbitrary budgets. The structural clause holds by construction of
`protocol5`. -/
theorem theorem_10 (ZK : (Bits → Bits → Bool) → (ℕ → ℕ) → Protocol) (hZK : ZKSpec ZK)
    (S : StrCom) (q : ℕ → ℕ) (hq : PolyBound q) (Bsrc : ℕ → ℕ → ℕ)
    (hS : IsExtractableStringCommitment S q Bsrc)
    (L : ℕ → PredLang) (hL : PredLang.PolyTime L)
    (Sched : List (Bool × Bits) → Bool × Bits → Bool)
    (hSched : PolyTimeBits fun x => match unpack x with
      | [h, p, c] => [Sched ((unpack h).map fun e => (e.headD false, e.tail)) (p.headD false, c)]
      | _ => [])
    (caller : Protocol) (pc : ℕ → ℕ) (hcaller : ResourceBound caller pc)
    (hcap : ∀ lam x, (caller.codeA lam x).CommitBitsLE (q lam) ∧ (caller.codeB lam x).CommitBitsLE (q lam))
    (Bout : ℕ → ℕ → ℕ) :
    Emulates
      (protocol5 S ZK L Sched q caller
        (fun lam b => if b < S.nb lam then S.group lam b
          else if b < 2 * S.nb lam then S.ng lam + S.group lam (b - S.nb lam)
          else 2 * S.ng lam + caller.group lam (b - 2 * S.nb lam))
        (fun lam => 2 * S.ng lam + caller.ng lam))
      trivialFunc
      (shiftCaller S caller
        (fun lam b => if b < S.nb lam then S.group lam b
          else if b < 2 * S.nb lam then S.ng lam + S.group lam (b - S.nb lam)
          else 2 * S.ng lam + caller.group lam (b - 2 * S.nb lam))
        (fun lam => 2 * S.ng lam + caller.ng lam))
      (idealCP L Sched)
      (fun lam b => decide (b < 2 * S.nb lam))
      (fun _ _ => Set.univ) (fun _ => True)
      (fun lam g => if g < 2 * S.ng lam then Bsrc lam (g % S.ng lam) else Bout lam (g - 2 * S.ng lam)) := by sorry

end DIObliviousTransfer
