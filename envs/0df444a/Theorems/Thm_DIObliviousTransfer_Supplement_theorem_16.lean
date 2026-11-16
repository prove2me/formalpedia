-- Prove2me | Theorems.Thm_DIObliviousTransfer_Supplement_theorem_16
-- name    : DIObliviousTransfer.Supplement.theorem_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:16:27.741831+00:00
-- url     : https://prove2.me/theorems/57429d97-746b-459e-a44b-8bcde8691e32
-- title:
--   Theorem 16 — one-window simulation-secure DI bit commitment (pinned-down)
-- statement:
--   Operator-requested pinned-down statement of Theorem 16, in the model of the published mission; the model choices are listed under Differences from the source.
--
--   Assume the hypotheses of Theorem 15: a code family meeting Lemmas 5–6, a bit commitment meeting Lemma 19, zero-knowledge proofs meeting Lemma 16, admissible constants $\gamma,\eta_{\mathrm{MS}},N_0$, and a polynomially bounded leakage parameter $\ell$. Let $S$ be Protocol 7 at capacity $q=1$, put $m=m_7(\lambda,\ell,1)$ and $L_1=kN_0m+\lceil m/200\rceil$, and let $\nu=\nu(N_0,\eta_{\mathrm{MS}})$ be the noise threshold of (8). Then Protocol 9 with source $S$ has the following properties.
--
--   1. **Simulation security for both parties (Definition 10).** Fix any honest committer caller with polynomial classical resources. Give the window the leakage budget $\lfloor m/100\rfloor$. Then Protocol 9 realizes the ideal bit commitment $\mathcal F_{\mathrm{BC}}$ against a corrupt committer and against a corrupt receiver. For every QPT adversary there is one QPT simulator that uses only the declared honest device interface of the source batch. For every polynomially bounded reference size and every QPT test, the distinguishing advantage between
--   $$\mathrm{Real}_{\text{Protocol 9},P^*}(\eta)\quad\text{and}\quad\mathrm{Ideal}_{\mathcal F_{\mathrm{BC}},\mathrm{Sim}}(\eta)$$
--   is bounded by one negligible function, uniformly over $\lambda$, the admissible initial state $\eta$ and the honest input.
--   2. **Correctness with constant honest-fault tolerance.** $\nu>0$, and there is a negligible $\varepsilon$ with the following property. For every honest device family whose loss on every coordinate and question pair is at most $q_{\mathrm{dev}}\le\nu/2$, and every bit $b$, the honest run that commits to $b$ and then opens ends with Bob outputting $b$, and Alice completing, with probability at least $1-\varepsilon(\lambda)$.
--   3. **One window of $O(\ell+\log^2\lambda)$ coordinates.** Protocol 9 declares one device batch, of $L_1$ coordinates. There is $c>0$ such that $L_1\le c(\ell+\log_2^2\lambda)$ for every $\lambda\ge2$ and every $\ell$.
--
--   The theorem adds simulation of the opening against a corrupt receiver to the string commitment of Theorem 15, with the same device budget. It is the one-window DI bit commitment the paper also uses for coin tossing.
--
--   Differences from the source:
--
--   - generalization: assume qOWFs (the assumptions of Theorem 15); the commitment of Lemma 19 and the ZK proofs of Lemma 16 → any bit commitment satisfying the conclusion of Lemma 19 (ComSpec) and any proof system satisfying the conclusion of Lemma 16 (ZKSpec); reason: Decision D14: the proof uses the primitives only through Lemmas 16 and 19, and under qOWFs the paper's instantiation meets both; as in the published Theorem 15
--   - generalization: AG codes on the Garcia–Stichtenoth tower over F₆₄ (inside the source Protocol 7) → any CodeFamily satisfying the conclusions of Lemmas 5 and 6 (CodeFamily.Spec); reason: Decision D15: the AG family satisfies the interface by Lemmas 5 and 6, so the statement specializes to the paper's
--   - generalization: γ, η_MS from Lemma 31 and a fixed integer N₀ ≥ max{166, ⌈200/(kγ)⌉} → every γ, η_MS > 0 satisfying the conclusion of Lemma 31 on [0.047/56, 1] and every integer N₀ ≥ max{166, 200/(6γ)}; reason: Decision D16: the ∀ form contains the paper's choice
--   - reading: Protocol 9 satisfies Definition 10 with auxiliary-input-uniform QPT simulators and negligible error → for either static corruption, every QPT adversary has one QPT simulator such that for every polynomially bounded reference size and QPT test there is one negligible ε bounding the advantage between the real execution of Protocol 9 and the ideal execution with idealBC, for every λ, admissible initial state η and honest input; the simulator has Dev_H on the source batch only; reason: Decisions D3, D4, D6–D9 (Definition 5) and D10: Definition 10 (i) is realization against a corrupt committer (the submitted bit is b∗, and idealBC can deliver only the opening of b∗), (ii) against a corrupt receiver (idealBC releases b only at the opening)
--   - reading: the guarantees permit sequential completed phases and delayed opening → realization holds for every honest committer caller with polynomial classical resources that issues the commit and, whenever it decides, the open command, flips coins but sends no messages and uses no devices of its own, and treats ⊥ as terminal; the receiver runs the prescribed receiver; reason: Decision D11, as for 'adaptive sequential phases' in the published Theorem 10; 'Rejection is terminal abort' (Protocol 9); interleaving with other protocols' messages is composition (Theorem 20), and an honest receiver of a bit commitment has no choices
--   - reading: correct bit commitment with negligible error; constant honest-fault tolerance, as for the source at q = 1 → for every honest device family with loss at most q_dev ≤ ν/2 per coordinate and question pair, the commit-then-open run on bit b ends with Alice outputting ∅ and Bob outputting b with probability at least 1 − ε(λ), ε negligible, where ν = nuOf N₀ η_MS > 0 is the source's threshold; reason: Decision D12, as in the published Theorem 15 at q = 1
--   - generalization: constant physical leakage rate, as for the source commitment at q = 1 → every leakage strategy of window cost at most ⌊m/100⌋ on every branch, m = m7(λ, ℓ, 1), for the window of LOf N₀ m coordinates; reason: Decision D24: the budget of the published Theorem 15 at q = 1, a fixed fraction of the window
--   - reading: O(ℓ + log² λ) coordinates → ∃ c > 0, ∀ λ ≥ 2, ∀ ℓ: L₁ = LOf N₀ (m7(λ, ℓ, 1)) ≤ c(ℓ + log₂² λ); reason: Decision D17: λ ≥ 2 since log₂² 1 = 0; c uniform in ℓ and λ; an upper bound only, as O(·) states
--   - encoding: one device window → the protocol declares one single-use batch (nb = 1) of L₁ coordinates; reason: Decision D22
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), Theorem 16, p.54 (PDF p.56); assumptions of Theorem 15, p.53 (PDF p.55); Definition 10, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_DIObliviousTransfer_protocol7
import Definitions.Def_DIObliviousTransfer_Supplement_protocol9

namespace DIObliviousTransfer

namespace Supplement

/-- **Theorem 16 (One-window simulation-secure DI bit commitment)**, Batra, Chen, Jain, Zhang,
arXiv:2610.01421 (held version, sha256 8334c039…), p.54 (PDF p.56). Under the assumptions of
Theorem 15, Protocol 9 satisfies Definition 10 with auxiliary-input-uniform QPT simulators and
negligible error. It uses one device window and `O(ℓ + log² λ)` coordinates, with constant
honest-fault tolerance and constant physical leakage rate, as for the source commitment at `q = 1`.

**Formalization Note** (decisions D3–D5, D10, D11, D12, D14–D17, D24 of the base mission).
"The assumptions of Theorem 15" are the hypotheses of the published `theorem_15`: a code family
with `CodeFamily.Spec` (D15), the interfaces `ComSpec` and `ZKSpec` in place of qOWFs (D14),
admissible constants `γ, η_MS, N₀` (D16) and a polynomially bounded leakage parameter `ℓ`; the
source is the published Protocol 7 at `q = 1`. Definition 10 is realization of `idealBC`
(`Emulates`, for either static corruption, one QPT simulator per adversary, negligible advantage
uniform over the admissible extension, the reference and the honest input), for every honest
committer caller with polynomial classical resources (sequential completed phases and delayed
opening), the simulator having `Dev_H` on the source batch only; correctness is negligible error
of the commit-then-open run for every honest device family with `q_dev ≤ ν/2` (D12). The window
budget is the source's at `q = 1`, `⌊m/100⌋` of the `L₁ = LOf N₀ m` coordinates with
`m = m7 λ ℓ 1` (D24; a constant physical leakage rate); the honest-fault threshold is the source's
`ν = nuOf N₀ η_MS > 0`. `O(ℓ + log² λ)` is an upper bound `c (ℓ + log₂² λ)` for one `c > 0`
uniform in `ℓ` and all `λ ≥ 2` (D17). -/
theorem theorem_16 (C : CodeFamily) (hC : C.Spec) (Com : BitCom) (hCom : ComSpec Com)
    (ZK : (Bits → Bits → Bool) → (ℕ → ℕ) → Protocol) (hZK : ZKSpec ZK)
    (γ ηMS : ℝ) (N₀ : ℕ) (hconst : AdmissibleConstants γ ηMS N₀)
    (ell : ℕ → ℕ) (hell : PolyBound ell) :
    -- Definition 10: simulation security for both parties, every honest committer caller
    (∀ (cA : ℕ → Bits → Code (Option Bits)) (pc : ℕ → ℕ), ResourceBound (bcCaller cA) pc →
      (∀ lam x, IsCommitterCaller (cA lam x)) →
      Emulates (protocol9 (protocol7 C Com ZK N₀ ηMS ell qOne) ZK cA) trivialFunc
        (bcCaller cA) idealBC
        (fun lam b => decide (b < (protocol7 C Com ZK N₀ ηMS ell qOne).nb lam))
        (fun _ _ => Set.univ) (fun _ => True)
        (fun lam _ => eraseCap (m7 lam (ell lam) 1))) ∧
    -- Definition 10: correctness with negligible error at q_dev ≤ ν/2, ν > 0
    0 < nuOf N₀ ηMS ∧
    (∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ Dv : HonestDevices, Dv.FaultLE (nuOf N₀ ηMS / 2) → ∀ (lam : ℕ) (b : Bool) (y : Bits),
        1 - ε lam ≤ honestEventProb
          (protocol9 (protocol7 C Com ZK N₀ ηMS ell qOne) ZK (fun _ x => bcCommitter x))
          trivialFunc Dv lam [b] y (fun o => o = (some [], some [b]))) ∧
    -- one device window of L₁ = LOf N₀ (m7 λ ℓ 1) coordinates, L₁ = O(ℓ + log² λ)
    (∀ cA : ℕ → Bits → Code (Option Bits), ∀ lam,
      (protocol9 (protocol7 C Com ZK N₀ ηMS ell qOne) ZK cA).nb lam = 1 ∧
      (protocol9 (protocol7 C Com ZK N₀ ηMS ell qOne) ZK cA).coords lam 0 =
        LOf N₀ (m7 lam (ell lam) 1)) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ lam : ℕ, 2 ≤ lam → ∀ ell' : ℕ,
      (LOf N₀ (m7 lam ell' 1) : ℝ) ≤ c * (ell' + Real.logb 2 lam ^ 2) := by sorry

end Supplement

end DIObliviousTransfer
