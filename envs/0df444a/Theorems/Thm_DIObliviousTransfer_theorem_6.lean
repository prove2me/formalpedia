-- Prove2me | Theorems.Thm_DIObliviousTransfer_theorem_6
-- name    : DIObliviousTransfer.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T09:12:43.54225+00:00
-- url     : https://prove2.me/theorems/46c13e82-2600-401e-8076-e518f676543a
-- title:
--   Theorem 6 — DI reduction from CP to OT
-- statement:
--   Under the schedule of Lemma 8 with admissible constants, Protocol 2 realizes ideal one-bit OT in the commit-and-prove hybrid, for either corruption. The security is computational, augmented and auxiliary-input-uniform, and it allows arbitrary joint device instruments and adaptive leakage of window cost up to $\lfloor m/100\rfloor$. The protocol uses one batch of $L=kN_0m+t_A$ coordinates. Its completeness error is negligible under (3) with $q_{\mathrm{dev}}\le\nu/2$, where $\nu>0$. It composes sequentially.
--
--   Differences from the source:
--
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
--   - encoding: under Theorem 22 → not a hypothesis: Theorem 22 is a separate milestone; the constants are AdmissibleConstants; reason: Theorem 22 is a theorem, used through the constants it provides
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), Theorem 6, p.31 (PDF p.33)

import Mathlib
import Definitions.Def_DIObliviousTransfer_protocol2
import Definitions.Def_DIObliviousTransfer_idealOT
import Definitions.Def_DIObliviousTransfer_Realizes

namespace DIObliviousTransfer

/-- **Theorem 6 (DI reduction from CP to OT)**, Batra, Chen, Jain, Zhang, arXiv:2610.01421 (held
version, sha256 8334c039…), p.31 (PDF p.33). Under the parameter schedule of Lemma 8 (constants
from Lemma 31 via Theorem 22), Protocol 2 realizes ideal(OT) in the CP hybrid with computational
augmented, auxiliary-input-uniform security: for each QPT corrupted party (either one) one QPT
simulator works for every admissible initial extension. It uses one batch of
`L = kN₀m + t_A` coordinates, permits arbitrary joint device instruments and the adaptive leakage
of Definition 3 (budget `⌊m/100⌋` on the window), has negligible completeness error under (3) with
`q_dev ≤ ν/2`, `ν > 0`, and composes sequentially at Definition 6.

**Formalization Note** (decisions D3–D13, D15, D16, D20–D24). The CP hybrid is `cp2`, ideal CP with
Protocol 2's predicate language and schedule. The leakage budget is `⌊m/100⌋` (D24), which covers
the prescribed `ℓ` (`m ≥ 100ℓ`) and a fixed positive fraction `c_local L` of the batch (Lemma 8).
"Under Theorem 22" is not a hypothesis: Theorem 22 is a separate milestone and fixes the constants
through `AdmissibleConstants`. -/
theorem theorem_6 (C : CodeFamily) (hC : C.Spec) (γ ηMS : ℝ) (N₀ : ℕ)
    (hconst : AdmissibleConstants γ ηMS N₀) (ell : ℕ → ℕ) (hell : PolyBound ell) :
    Realizes (protocol2 C N₀ ηMS ell) (cp2 C N₀ ell) idealOT (fun _ => True)
        (fun lam _ => eraseCap (mOT lam (ell lam))) ∧
    (∀ lam, (protocol2 C N₀ ηMS ell).nb lam = 1 ∧
      (protocol2 C N₀ ηMS ell).coords lam 0 = LOf N₀ (mOT lam (ell lam))) ∧
    0 < nuOf N₀ ηMS ∧
    ∃ ε : ℕ → ℝ, Negligible ε ∧
      CorrectWithin (protocol2 C N₀ ηMS ell) (cp2 C N₀ ell) idealOT (nuOf N₀ ηMS / 2) ε ∧
      ComposesSequentially (protocol2 C N₀ ηMS ell) (cp2 C N₀ ell) idealOT (fun _ => True)
        (fun lam _ => eraseCap (mOT lam (ell lam))) (nuOf N₀ ηMS / 2) ε := by sorry

end DIObliviousTransfer
