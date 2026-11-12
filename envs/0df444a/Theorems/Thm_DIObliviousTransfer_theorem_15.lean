-- Prove2me | Theorems.Thm_DIObliviousTransfer_theorem_15
-- name    : DIObliviousTransfer.theorem_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T09:14:46.064182+00:00
-- url     : https://prove2.me/theorems/1350946f-0872-48bf-9b0e-2fe37286766e
-- title:
--   Theorem 15 — one-window extractable DI string commitment
-- statement:
--   Let $1\le q\le\mathrm{poly}(\lambda)$ and $\ell\le\mathrm{poly}(\lambda)$, and size the schedule of Lemma 8 also for $m\ge100q$. Then Protocol 7, with leakage budget $\lfloor m/100\rfloor$ on its window:
--   1. satisfies Definition 9, with polynomial-resource honest algorithms;
--   2. uses one device window of $L_q=\Theta(q+\ell+\log^2\lambda)$ coordinates;
--   3. is correct with negligible error under (3) with $q_{\mathrm{dev}}\le\nu/2$, where $\nu>0$ depends on neither $q$, $m$ nor $\lambda$.
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
--   - generalization: independent honest quantum coordinate implementations with loss at most q_dev for every question pair (3) → honest devices given by independent per-coordinate conditional answer distributions with loss at most q_dev, not required to be quantum or no-signalling; reason: Decision D12: correctness uses only (3) and independence (Claim 3); quantum devices are a special case
--   - reading: total classical computation and communication polynomial in λ → each party's next-action function is computed by a polynomial-time Turing machine and every branch has polynomially many operations and sent bits; reason: Decision D13; uniform rather than circuit size, the stronger reading
--   - reading: L = Θ(ℓ + log² λ) → ∃ c₁ c₂ > 0, ∀ λ ≥ 2, ∀ ℓ: c₁(ℓ + log₂²λ) ≤ L ≤ c₂(ℓ + log₂²λ); reason: Decision D17: λ ≥ 2 since log₂²1 = 0; uniform in ℓ, the stronger reading
--   - encoding: bounded samplers with fixed polynomial clocks → six fair bits per field element; nonzero elements by at most m rejections then 1; uniform elements of [0,N) by rejection capped at λ trials with fallback 0; orderings by Fisher–Yates and size-t sets as the first t entries of a uniform ordering; reason: Decision D20 (p.27)
--   - encoding: R_DI ≤ 3 single-use device windows; arbitrary joint device measurements → the protocol declares three batches, each usable once; device programs are arbitrary QPT instruments on their whole batch; reason: Decision D22
--   - encoding: all prescribed interparty messages are classical → messages have type Bits; reason: Decision D23; holds by type
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), Theorem 15, p.53 (PDF p.55)

import Mathlib
import Definitions.Def_DIObliviousTransfer_protocol7

namespace DIObliviousTransfer

/-- **Theorem 15 (One-window extractable DI string commitment)**, Batra, Chen, Jain, Zhang,
arXiv:2610.01421 (held version, sha256 8334c039…), p.53 (PDF p.55). For every public
`1 ≤ q ≤ poly(λ)` and physical-window budget `ℓ ≤ poly(λ)`, with the packed schedule of Lemma 8
sized also for `m ≥ 100q`, Protocol 7 satisfies Definition 9 with strict-QPT algorithms and
auxiliary-input-uniform simulators. It uses one device window and `L_q = Θ(q + ℓ + log² λ)`
coordinates; there are fixed positive local noise and leakage fractions under (3) with
`q_dev ≤ ν/2` and the stated physical-window leakage model, neither depending on `q, m, λ`.

**Formalization Note** (decisions D3–D9, D12–D17, D20, D24). "Assume qOWFs" is replaced by the
interfaces of Lemmas 16 and 19 (`ZKSpec`, `ComSpec`). The window budget is `⌊m/100⌋` (D24).
"Strict-QPT algorithms" are the polynomial resource bounds of the honest controllers in either
role; correctness is `StrCom.CorrectAt` with negligible error at `q_dev ≤ ν/2`, `ν > 0` depending
only on `N₀, η_MS`. `Θ` is uniform in `q ≥ 1` and `ℓ` for `λ ≥ 2` (D17). -/
theorem theorem_15 (C : CodeFamily) (hC : C.Spec) (Com : BitCom) (hCom : ComSpec Com)
    (ZK : (Bits → Bits → Bool) → (ℕ → ℕ) → Protocol) (hZK : ZKSpec ZK)
    (γ ηMS : ℝ) (N₀ : ℕ) (hconst : AdmissibleConstants γ ηMS N₀)
    (q ell : ℕ → ℕ) (hq : PolyBound q) (hq1 : ∀ lam, 1 ≤ q lam) (hell : PolyBound ell) :
    IsExtractableStringCommitment (protocol7 C Com ZK N₀ ηMS ell q) q
        (fun lam _ => eraseCap (m7 lam (ell lam) (q lam))) ∧
    (∀ lam, (protocol7 C Com ZK N₀ ηMS ell q).nb lam = 1 ∧
      (protocol7 C Com ZK N₀ ηMS ell q).coords lam 0 = LOf N₀ (m7 lam (ell lam) (q lam))) ∧
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ lam : ℕ, 2 ≤ lam → ∀ q' ell' : ℕ, 1 ≤ q' →
      c₁ * (q' + ell' + Real.logb 2 lam ^ 2) ≤ (LOf N₀ (m7 lam ell' q') : ℝ) ∧
      (LOf N₀ (m7 lam ell' q') : ℝ) ≤ c₂ * (q' + ell' + Real.logb 2 lam ^ 2)) ∧
    0 < nuOf N₀ ηMS ∧
    (∃ ε : ℕ → ℝ, Negligible ε ∧
      (protocol7 C Com ZK N₀ ηMS ell q).CorrectAt q (nuOf N₀ ηMS / 2) ε) ∧
    ∃ p : ℕ → ℕ, ResourceBound ((protocol7 C Com ZK N₀ ηMS ell q).proto true) p ∧
      ResourceBound ((protocol7 C Com ZK N₀ ηMS ell q).proto false) p := by sorry

end DIObliviousTransfer
