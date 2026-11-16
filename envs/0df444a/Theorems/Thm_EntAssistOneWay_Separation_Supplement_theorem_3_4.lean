-- Prove2me | Theorems.Thm_EntAssistOneWay_Separation_Supplement_theorem_3_4
-- name    : EntAssistOneWay.Separation.Supplement.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:51:07.466719+00:00
-- url     : https://prove2.me/theorems/9bfbd1e6-fd07-488b-b563-8311d5c60130
-- title:
--   Theorem 3.4 — classical SMP simulation of entanglement-assisted protocols
-- statement:
--   Fix $\eta>0$. There is a constant $K>0$, depending on $\eta$ only, such that the following holds for all finite input sets $X,Y$, all local dimensions $d_A,d_B$ and every $C\ge0$.
--
--   1. Every interactive entanglement-assisted protocol $\Pi$ with $C$ bits of communication (arbitrary shared state, arbitrary speaker order) has a classical SMP simulation $\Pi'$ with shared randomness between the players only, using $c_A+c_B$ bits, such that
--   $$c_A+c_B\le K\cdot2^{2C}\qquad\text{and}\qquad\big|\Pr[\Pi'\text{ accepts}\mid x,y]-\Pr[\Pi\text{ accepts}\mid x,y]\big|\le\eta\quad\text{for all }x,y.$$
--   2. If $\Pi$ is one-way (Alice to Bob), the same holds with $c_A+c_B\le K\cdot 2^C$.
--
--   The SMP referee may use a private coin. The theorem gives the exponent of the known exponential simulation exactly, and it is what makes an entanglement-assisted protocol with $O(\log n)$ bits yield an unassisted SMP protocol with $\mathrm{poly}(n)$ bits.
--
--   **Formalization Note** The paper writes $O(2^{2C})$ and $O(2^C)$ for fixed $\eta$; here one constant $K=K(\eta)$, chosen before $C$, the input sets, the dimensions and the protocol, bounds both clauses for every $C\ge0$.
--
--   Differences from the source:
--   - encoding: an entanglement-assisted protocol using C bits (interactive, any speaker order, any local operations) → InteractiveEAProtocol: exactly C bits, speaker fixed by the transcript prefix, two-outcome Kraus instruments with m Kraus operators (all m quantified), final binary effect by a party fixed by the transcript; reason: shorter transcripts pad with trivial instruments; ancillas and private coins are absorbed into the local dimensions and instruments; every completely positive map has a finite Kraus form
--   - encoding: O(2^{2C}) and O(2^C) bits for fixed η → ∃ K > 0 depending on η only, quantified before C, X, Y, dA, dB and the protocol, with bounds K·2^(2C) and K·2^C for every C ≥ 0 (one K for both clauses); reason: the O(·) is for fixed η and the proof's bound is uniform in C; the maximum of two constants serves both clauses
--   - encoding: classical SMP protocol with shared randomness (between the players only) → RandomizedSMPProtocol: seed on an arbitrary probability space, measurable message maps, referee accepting with probability q(a,b) ∈ [0,1]; reason: §3.1's model; the referee's private coin is the one the proof uses
--   - encoding: finite input sets and C-bit messages → Fintype inputs where the source assumes them; message indices Fin (2^c); reason: labels every message of the stated length; same instances
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), p. 17, Theorem 3.4; pp. 17–19, proof

import Definitions.Def_EntAssistOneWay_Separation_Supplement_InteractiveEA
import Definitions.Def_EntAssistOneWay_Separation_Supplement_OneWayEA
import Definitions.Def_EntAssistOneWay_Separation_Supplement_RandomizedSMP

open scoped BigOperators ComplexOrder
open Classical
set_option autoImplicit false

namespace EntAssistOneWay.Separation.Supplement

noncomputable section

/-- Theorem 3.4, p. 17: for each fixed `η > 0`, one constant `K` (depending on `η` only)
bounds the cost of a classical shared-randomness SMP simulation, within `η` in acceptance
probability on every input, of every entanglement-assisted protocol with `C` bits:
`K · 2^{2C}` bits in general, `K · 2^C` bits for one-way protocols. -/
theorem theorem_3_4 :
    ∀ η : ℝ, 0 < η → ∃ K : ℝ, 0 < K ∧
      (∀ (X Y : Type) [Fintype X] [Fintype Y] (dA dB m C : ℕ)
          (P : InteractiveEAProtocol X Y dA dB m C),
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (cA cB : ℕ)
          (Q : RandomizedSMPProtocol X Y Ω cA cB),
          ((cA + cB : ℕ) : ℝ) ≤ K * 2 ^ (2 * C) ∧
          ∀ x y, |randomizedSMPAccept Q x y - interactiveAccept P x y| ≤ η) ∧
      (∀ (X Y : Type) [Fintype X] [Fintype Y] (dA dB C : ℕ)
          (P : OneWayEAProtocol X Y dA dB C),
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (cA cB : ℕ)
          (Q : RandomizedSMPProtocol X Y Ω cA cB),
          ((cA + cB : ℕ) : ℝ) ≤ K * 2 ^ C ∧
          ∀ x y, |randomizedSMPAccept Q x y - oneWayAccept P x y| ≤ η) := by sorry

end

end EntAssistOneWay.Separation.Supplement
