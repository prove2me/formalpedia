-- Prove2me | Theorems.Thm_DepthOptQC_Synth_Supplement_theorem_12
-- name    : DepthOptQC.Synth.Supplement.theorem_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:50:17.210638+00:00
-- url     : https://prove2.me/theorems/762f080a-96fa-46cc-b257-658bda8c177b
-- title:
--   Theorem 12 — depth-preserving real decision simulation
-- statement:
--   Uniform constants $K>0$ and $k\in\mathbb N$ work simultaneously for the four model pairs
--   $$(\mathrm{QUAC},\mathrm{QRAC}),\ (\mathrm{QUAC}_f,\mathrm{QRAC}_f),\ (\mathrm{QUTC},\mathrm{QRTC}),\ (\mathrm{QUTC}_f,\mathrm{QRTC}_f).$$
--   If $C$ is a depth-$d$ circuit in the universal member of a pair and $s\ge2$ bounds both its gate count and width, then for every $\varepsilon\in(0,1/2)$ there is a circuit $\widetilde C$ in the corresponding real class with depth at most $K(d+1)$ and size at most $K(s+1/\varepsilon)^k$, such that
--   $$
--   |p_{\widetilde C}(x)-p_C(x)|\le\varepsilon
--   $$
--   for every classical input $x$.
--
--   This result preserves the designated-output decision probability; it does not claim operator-norm approximation of the original complex unitary.
--
--   Differences from the source:
--   - reading: $O(d+1)$ and $\operatorname{poly}(s,1/\varepsilon)$ → uniform witnesses $K,k$ shared by all four finite model pairs; reason: explicit meaning of the printed asymptotics
--   - encoding: circuit class notation → exact layered gate alphabets, fresh zero workspace and a designated output field; reason: operational expansion of Definitions 1–3 and Eq. (1)
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, Theorem 12, p.49 (PDF p.51), Eq. (230)

import Definitions.Def_DepthOptQC_Synth_Supplement_CircuitModel

set_option autoImplicit false

namespace DepthOptQC.Synth.Supplement

open QAlgorithms

/-- **Theorem 12 (Depth-Preserving Real Decision Simulation)** — Vasconcelos,
arXiv:2609.34659, p.49, Eq. (230). Each of QUAC, QUACf, QUTC and QUTCf has an acceptance-preserving
simulation in the corresponding real model QRAC, QRACf, QRTC or QRTCf, with constant-factor depth
and polynomial size.

**Formalization Note.** `WideModel` indexes all four pairs. The compiled circuit is selected before
the classical input; only designated-output acceptance probability, not the full unitary, is
approximated. -/
theorem theorem_12 :
    ∃ K : ℝ, 0 < K ∧ ∃ k : ℕ,
      ∀ (M : WideModel) (n d s : ℕ) (C : DecisionCircuit (universalWideGateSet M) n),
        2 ≤ s → C.depth = d → C.size ≤ s → C.width ≤ s →
        ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
          ∃ Ctilde : DecisionCircuit (realWideGateSet M) n,
            (Ctilde.depth : ℝ) ≤ K * (d + 1) ∧
            (Ctilde.size : ℝ) ≤ K * ((s : ℝ) + 1 / ε) ^ k ∧
            ∀ x : Qubits n, |Ctilde.acceptance x - C.acceptance x| ≤ ε := by sorry

end DepthOptQC.Synth.Supplement
