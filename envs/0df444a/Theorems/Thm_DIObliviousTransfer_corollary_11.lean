-- Prove2me | Theorems.Thm_DIObliviousTransfer_corollary_11
-- name    : DIObliviousTransfer.corollary_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T09:16:46.164864+00:00
-- url     : https://prove2.me/theorems/d12dbb81-201a-4b7e-92ef-e667cc16fd24
-- title:
--   Corollary 11 — OT from two preprocessing commitments
-- statement:
--   Assume the hypotheses of Theorem 6 and zero-knowledge proofs as in Lemma 16. Let the source be any correct, extractable string commitment (Definition 9) of capacity $q_{\mathrm{bank}}=10L_0$ (20). Then two sequential preprocessing commitments, followed by Protocol 2 with Protocol 5, realize one-bit OT with auxiliary-input-uniform QPT simulation and negligible error. The commit-and-prove phases use no devices after preprocessing.
--
--   Differences from the source:
--
--   - generalization: assume qOWFs; the commitment of Lemma 19 (BCKM on Naor) and the ZK proofs of Lemma 16 (GMW on Naor) → any bit commitment satisfying the conclusion of Lemma 19 (ComSpec) and any proof system satisfying the conclusion of Lemma 16 (ZKSpec); reason: Decision D14: the proof uses the primitives only through Lemmas 16 and 19, and under qOWFs the paper's instantiation meets both (Lemma 16 is the milestone linking ZK to qOWFs)
--   - generalization: AG codes B = D = ev_P L(G), A = ev_P L(2G) on the Garcia–Stichtenoth tower over F₆₄ → any CodeFamily satisfying the conclusions of Lemmas 5 and 6 (CodeFamily.Spec); reason: Decision D15: the AG family satisfies the interface by Lemmas 5 and 6, so the statement specializes to the paper's
--   - generalization: γ, η_MS from Lemma 31 and a fixed integer N₀ ≥ max{166, ⌈200/(kγ)⌉} → every γ, η_MS > 0 satisfying the conclusion of Lemma 31 on [0.047/56, 1] and every integer N₀ ≥ max{166, 200/(6γ)}; reason: Decision D16: the ∀ form contains the paper's choice
--   - generalization: the prescribed physical-window budget ℓ and fixed positive leakage fractions → every leakage strategy of window cost at most ⌊m/100⌋ on every branch; reason: Decision D24: m ≥ 100ℓ and c_local L ≤ m/100 (Lemma 8), and ⌊m/100⌋ is the bound the proof uses
--   - reading: nonuniform QPT adversaries, devices and simulators with polynomial-size quantum advice → families of machines whose activations are circuits of at most two-qubit unitaries and single-wire resets with classical input loaded and output measured, all sizes bounded by one polynomial in λ; advice is part of the arbitrary initial state; reason: Decision D3 (pp.2, 17): one standard reading of nonuniform QPT
--   - reading: Real ≈c Ideal, the negligible advantage bound uniform over admissible η and fixed honest inputs → for every polynomially bounded reference size and every QPT test there is one negligible ε with advantage at most ε(λ) for every λ, every admissible η and every valid honest input; reason: Decision D4 (Definition 5 (ii)); the stronger, uniform reading
--   - reading: adaptive bidirectional messages of total cost at most ℓ qubits, every adaptive control symbol charged in a self-delimiting transcript, fixed public schedule free → window steps emitting a control symbol (classical length, quantum length, next active side), scheduled or adaptive; cost = classical bits + Elias-γ encodings of adaptive control symbols + qubits; a message exceeding the remaining budget closes the window undelivered; reason: Decision D5 (Definition 3 (i)-(ii)); enforcing the budget is equivalent to quantifying over admissible strategies since both sides see the control transcript
--   - encoding: admissible initial extension η on I_H W_H K_H D_A D_B P R with classical honest input, blank workspace and fresh coins → an arbitrary density operator on (corrupt register, honest batch registers, reference); honest input, workspace and coins are classical values of the honest controller that no other component can access; reason: Decision D6 (Definition 4); same instances
--   - encoding: compared states (corrupt final cq-state, honest input/output, public transcript, R) → the cq state (honest input, honest output, transcript) ⊗ (corrupt register, R); honest batch registers and simulator scratch traced out; reason: Decision D7 (Definition 5 (i))
--   - reading: declared honest device interface Dev_H: only the prescribed classical device operations and leakage window, no reset, copy or re-preparation → the simulator may use each honest batch once, choosing its questions and playing the corrupt side of its window, and receives the answers; reason: Decision D8 (Definition 5 (iii))
--   - reading: ∃Sim after ∀P∗, receiving the corrupt workspace and devices and ideal releases, acting as Sim ⊗ id_R → the simulator is chosen after the adversary, is a QPT machine on the corrupt register plus fresh qubits, never acts on R, and outputs the transcript; reason: Decision D9 (Definition 5 (iv))
--   - encoding: ideal functionalities as prose interfaces; CP with Boolean-circuit predicates and an authorized predicate schedule → deterministic classical state machines with party and adversary ports; CP over a predicate language (projections and the protocol's predicates) and a schedule predicate; reason: Decision D10 (Definitions 7, 8); honest parties and in-schedule requests only use the prescribed predicates
--   - encoding: composition at invocation boundaries satisfying Definition 6 in every replacement hybrid → ideal calls replaced by fresh copies of the subprotocol on fresh batches with fresh budget groups; Definition 6 holds by construction of the execution semantics; reason: Decision D11 (Definition 6, Theorem 20)
--   - generalization: independent honest quantum coordinate implementations with loss at most q_dev for every question pair (3) → honest devices given by independent per-coordinate conditional answer distributions with loss at most q_dev, not required to be quantum or no-signalling; reason: Decision D12: correctness uses only (3) and independence (Claim 3); quantum devices are a special case
--   - encoding: bounded samplers with fixed polynomial clocks → six fair bits per field element; nonzero elements by at most m rejections then 1; uniform elements of [0,N) by rejection capped at λ trials with fallback 0; orderings by Fisher–Yates and size-t sets as the first t entries of a uniform ordering; reason: Decision D20 (p.27)
--   - encoding: R_DI ≤ 3 single-use device windows; arbitrary joint device measurements → the protocol declares three batches, each usable once; device programs are arbitrary QPT instruments on their whole batch; reason: Decision D22
--   - encoding: all prescribed interparty messages are classical → messages have type Bits; reason: Decision D23; holds by type
--   - reading: under Definition 9 → the source is extractable with its window budgets and correct with negligible error at q_dev ≤ ν/2; reason: Definition 9 concerns a correct string commitment; correctness is needed for negligible honest error
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), Corollary 11, p.41 (PDF p.43), with (20)

import Mathlib
import Definitions.Def_DIObliviousTransfer_protocol12
import Definitions.Def_DIObliviousTransfer_idealOT

namespace DIObliviousTransfer

/-- **Corollary 11 (OT from two preprocessing commitments)**, Batra, Chen, Jain, Zhang,
arXiv:2610.01421 (held version, sha256 8334c039…), p.41 (PDF p.43). Under Definition 9 and the
hypotheses of Theorem 6, two sequential preprocessing commitments of capacity (20)
(`q_A, q_B ≤ q_bank = 10L₀`), followed by Protocol 2 with Protocol 5, realize one-bit OT with
auxiliary-input-uniform QPT simulation and negligible error. The CP phases use no devices after
preprocessing.

**Formalization Note** (decisions D11, D12, D14, D15, D16, D24). The source is any string
commitment that is extractable (Definition 9) with its window budgets `Bsrc` and correct with
negligible error at the honest noise `q_dev ≤ ν/2` (Definition 9's "correct string commitment");
the transfer window has budget `⌊m₀/100⌋` (D24). Each source invocation and the transfer batch
have separate budget groups. "Under qOWFs" enters through the ZK interface (`ZKSpec`). The last
sentence holds by construction (`protocol5`). -/
theorem corollary_11 (C : CodeFamily) (hC : C.Spec)
    (ZK : (Bits → Bits → Bool) → (ℕ → ℕ) → Protocol) (hZK : ZKSpec ZK)
    (γ ηMS : ℝ) (N₀ : ℕ) (hconst : AdmissibleConstants γ ηMS N₀) (ell : ℕ → ℕ)
    (hell : PolyBound ell) (S : StrCom) (Bsrc : ℕ → ℕ → ℕ)
    (hS : IsExtractableStringCommitment S (qbankFn N₀ ell) Bsrc)
    (εS : ℕ → ℝ) (hεS : Negligible εS) (hcorr : S.CorrectAt (qbankFn N₀ ell) (nuOf N₀ ηMS / 2) εS) :
    Realizes (protocol12' S C ZK N₀ ηMS ell) trivialFunc idealOT (fun _ => True)
        (fun lam g => if g < 2 * S.ng lam then Bsrc lam (g % S.ng lam)
          else eraseCap (mOT lam (ell lam))) ∧
    ∃ ε : ℕ → ℝ, Negligible ε ∧
      CorrectWithin (protocol12' S C ZK N₀ ηMS ell) trivialFunc idealOT (nuOf N₀ ηMS / 2) ε := by sorry

end DIObliviousTransfer
