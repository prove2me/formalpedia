-- Prove2me | Theorems.Thm_DIObliviousTransfer_theorem_18
-- name    : DIObliviousTransfer.theorem_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T09:17:02.504254+00:00
-- url     : https://prove2.me/theorems/1386ea0d-b851-46bc-9833-264c9dd6c855
-- title:
--   Theorem 18 — robust DI OT in three device windows (pinned-down)
-- statement:
--   Operator-requested pinned-down statement of Theorem 18; the model choices are listed under Differences from the source.
--
--   Let $\ell$ be polynomially bounded and the constants admissible, and set the sizes by (26). Then Protocol 12 realizes one-bit OT:
--   $$\forall\text{ static }P^*\in\mathrm{QPT}\ \exists\mathrm{Sim}\in\mathrm{QPT}\ \forall\eta^{\mathcal R}_{\mathrm{adm}}:\ \mathrm{Real}_{\mathcal P,P^*}(\eta^{\mathcal R}_{\mathrm{adm}})\approx_c\mathrm{Ideal}_{\mathrm{OT,Sim}}(\eta^{\mathcal R}_{\mathrm{adm}}),$$
--   for either corruption. Simulation is auxiliary-input-uniform and allows arbitrary joint device measurements. The total physical-window leakage budget $\max(\ell,\lfloor c_{\mathrm{global}}L_{\mathrm{total}}\rfloor)$ is shared by the three windows in any adaptive distribution.
--
--   In addition:
--   1. the protocol admits efficient sequential composition;
--   2. $R_{\mathrm{DI}}\le3$ and $L_{\mathrm{total}}=2L_{\mathrm{pre}}+L_0=\Theta(\ell+\log^2\lambda)$ (27);
--   3. honest correctness has negligible error under (3) with $q_{\mathrm{dev}}\le\nu_0:=\nu_{\mathrm{global}}/2>0$;
--   4. interparty messages are classical, and total classical computation and communication are polynomial in $\lambda$.
--
--   Differences from the source:
--
--   - generalization: assume qOWFs; the commitment of Lemma 19 (BCKM on Naor) and the ZK proofs of Lemma 16 (GMW on Naor) → any bit commitment satisfying the conclusion of Lemma 19 (ComSpec) and any proof system satisfying the conclusion of Lemma 16 (ZKSpec); reason: Decision D14: the proof uses the primitives only through Lemmas 16 and 19, and under qOWFs the paper's instantiation meets both (Lemma 16 is the milestone linking ZK to qOWFs)
--   - generalization: AG codes B = D = ev_P L(G), A = ev_P L(2G) on the Garcia–Stichtenoth tower over F₆₄ → any CodeFamily satisfying the conclusions of Lemmas 5 and 6 (CodeFamily.Spec); reason: Decision D15: the AG family satisfies the interface by Lemmas 5 and 6, so the statement specializes to the paper's
--   - generalization: γ, η_MS from Lemma 31 and a fixed integer N₀ ≥ max{166, ⌈200/(kγ)⌉} → every γ, η_MS > 0 satisfying the conclusion of Lemma 31 on [0.047/56, 1] and every integer N₀ ≥ max{166, 200/(6γ)}; reason: Decision D16: the ∀ form contains the paper's choice
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
--   - reading: total classical computation and communication polynomial in λ → each party's next-action function is computed by a polynomial-time Turing machine and every branch has polynomially many operations and sent bits; reason: Decision D13; uniform rather than circuit size, the stronger reading
--   - reading: L = Θ(ℓ + log² λ) → ∃ c₁ c₂ > 0, ∀ λ ≥ 2, ∀ ℓ: c₁(ℓ + log₂²λ) ≤ L ≤ c₂(ℓ + log₂²λ); reason: Decision D17: λ ≥ 2 since log₂²1 = 0; uniform in ℓ, the stronger reading
--   - generalization: a total physical-window leakage budget at most c_global L_total, regardless of its distribution among the three windows, with Definition 11's Σ_j ℓ_j ≤ ℓ → one budget group shared by the three windows, with budget max(ℓ, ⌊c_global L_total⌋) on every branch, distributed adaptively; reason: Decision D19: adaptive per-branch distribution contains every fixed split
--   - encoding: bounded samplers with fixed polynomial clocks → six fair bits per field element; nonzero elements by at most m rejections then 1; uniform elements of [0,N) by rejection capped at λ trials with fallback 0; orderings by Fisher–Yates and size-t sets as the first t entries of a uniform ordering; reason: Decision D20 (p.27)
--   - encoding: R_DI ≤ 3 single-use device windows; arbitrary joint device measurements → the protocol declares three batches, each usable once; device programs are arbitrary QPT instruments on their whole batch; reason: Decision D22
--   - encoding: all prescribed interparty messages are classical → messages have type Bits; reason: Decision D23; holds by type
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), Theorem 18, p.56 (PDF p.58)

import Mathlib
import Definitions.Def_DIObliviousTransfer_protocol12
import Definitions.Def_DIObliviousTransfer_idealOT

namespace DIObliviousTransfer

/-- **Theorem 18 (Robust DI OT in three device windows)**, Batra, Chen, Jain, Zhang,
arXiv:2610.01421 (held version, sha256 8334c039…), p.56 (PDF p.58), the operator-requested
pinned-down statement. Under (26) for a polynomially bounded `ℓ`, Protocol 12 realizes one-bit OT
with `∀` static `P∗ ∈ QPT ∃Sim ∈ QPT ∀η^𝓡_adm : Real_{𝒫,P∗}(η) ≈c Ideal_{OT,Sim}(η)`, for either
corruption, auxiliary-input-uniformly, with arbitrary joint device measurements and a total
physical-window leakage budget `max(ℓ, ⌊c_global L_total⌋)` shared by the three windows in any
adaptive distribution; it admits efficient sequential composition; `R_DI ≤ 3`,
`L_total = 2L_pre + L₀ = Θ(ℓ + log² λ)`; honest correctness has negligible error under (3) with
`q_dev ≤ ν₀ := ν_global/2 > 0`; interparty messages are classical and total classical computation
and communication are polynomial in `λ`.

**Formalization Note** (decisions D1–D24). qOWFs enter through the interfaces of Lemma 16 (`ZKSpec`,
derived from qOWFs by Lemma 16) and Lemma 19 (`ComSpec`), and the AG codes through `CodeFamily.Spec`
(D14, D15). The constants are any admissible `γ, η_MS, N₀` (D16), fixed before `λ` and `ℓ`.
Security quantifies `∀P∗ ∃Sim ∀n_R ∀D ∃ε ∀λ ∀η ∀inputs` (D4, D18); the budget group is shared by
the three windows and control symbols are charged (D5, D19). `R_DI` is the number of declared
single-use batches (D22). Messages are of type `Bits` (D23); device programs are arbitrary
instruments on their whole batch (D22). -/
theorem theorem_18 (C : CodeFamily) (hC : C.Spec) (Com : BitCom) (hCom : ComSpec Com)
    (ZK : (Bits → Bits → Bool) → (ℕ → ℕ) → Protocol) (hZK : ZKSpec ZK)
    (γ ηMS : ℝ) (N₀ : ℕ) (hconst : AdmissibleConstants γ ηMS N₀)
    (ell : ℕ → ℕ) (hell : PolyBound ell) :
    -- security for either static corruption, with the shared total leakage budget
    Realizes (protocol12 C Com ZK N₀ ηMS ell) trivialFunc idealOT (fun _ => True)
        (fun lam _ => max (ell lam) ⌊cGlobal N₀ * Ltotal N₀ lam (ell lam)⌋₊) ∧
    -- the device bounds (27): three single-use batches of sizes L_pre, L_pre, L₀
    (∀ lam, (protocol12 C Com ZK N₀ ηMS ell).nb lam = 3 ∧
      (protocol12 C Com ZK N₀ ηMS ell).coords lam 0 = LPreOf N₀ lam (ell lam) ∧
      (protocol12 C Com ZK N₀ ηMS ell).coords lam 1 = LPreOf N₀ lam (ell lam) ∧
      (protocol12 C Com ZK N₀ ηMS ell).coords lam 2 = L0Of N₀ lam (ell lam) ∧
      Ltotal N₀ lam (ell lam) = 2 * LPreOf N₀ lam (ell lam) + L0Of N₀ lam (ell lam)) ∧
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ lam : ℕ, 2 ≤ lam → ∀ ell' : ℕ,
      c₁ * (ell' + Real.logb 2 lam ^ 2) ≤ (Ltotal N₀ lam ell' : ℝ) ∧
      (Ltotal N₀ lam ell' : ℝ) ≤ c₂ * (ell' + Real.logb 2 lam ^ 2)) ∧
    -- honest correctness at q_dev ≤ ν₀ = ν_global/2 > 0, and sequential composition
    0 < nuGlobal N₀ ηMS / 2 ∧
    (∃ ε : ℕ → ℝ, Negligible ε ∧
      CorrectWithin (protocol12 C Com ZK N₀ ηMS ell) trivialFunc idealOT (nuGlobal N₀ ηMS / 2) ε ∧
      ComposesSequentially (protocol12 C Com ZK N₀ ηMS ell) trivialFunc idealOT (fun _ => True)
        (fun lam _ => max (ell lam) ⌊cGlobal N₀ * Ltotal N₀ lam (ell lam)⌋₊)
        (nuGlobal N₀ ηMS / 2) ε) ∧
    -- polynomial classical computation and communication
    ∃ p : ℕ → ℕ, ResourceBound (protocol12 C Com ZK N₀ ηMS ell) p := by sorry

end DIObliviousTransfer
