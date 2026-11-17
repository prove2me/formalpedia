-- Prove2me | Theorems.Thm_DepthOptQC_Synth_Supplement_theorem_15
-- name    : DepthOptQC.Synth.Supplement.theorem_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:53:07.965461+00:00
-- url     : https://prove2.me/theorems/fb8fa3a6-3054-43f5-924f-53f1e9f041fb
-- title:
--   Theorem 15 — structured Fourier representations of standard circuits
-- statement:
--   Uniform constants $K>0$ and $k\in\mathbb N$ give the following representations.
--
--   1. A depth-$d$ circuit in QAC, QACf, QTC or QTCf, whose gate count and width are bounded by $s\ge2$, has for every $\varepsilon\in(0,1/2)$ a structured Fourier circuit over the corresponding family $\mathcal A,\mathcal A_f,\mathcal T$ or $\mathcal T_f$. It has at most $K(d+1)$ phase layers and polynomial width and description length.
--   2. For QUNC and QUNCf the corresponding families are $\mathcal A_3$ and $\mathcal A_{3,f}$; QNCf also uses $\mathcal A_{3,f}$. These circuits have at most $K(d+1+\log_2\log_2(s/\varepsilon))$ phase layers and polynomial width and description length.
--
--   In every case the structured circuit and its designated output are chosen before the input and satisfy
--   $$|p_U(x)-p_C(x)|\le\varepsilon$$
--   for every $x\in\{0,1\}^n$.
--
--   Differences from the source:
--   - reading: all $O$ and polynomial bounds → uniform witnesses $K,k$ shared across the finite list of model clauses; reason: explicit printed asymptotics
--   - encoding: structured phase families described in prose → exact affine-plus-disjoint-block syntax with bounded-AND, AND, Threshold and controlled-Parity blocks; reason: Definitions 5–7 expanded operationally
--   - encoding: size and description length $\operatorname{poly}(s,1/\varepsilon)$ → a concrete finite syntax-description count is polynomially bounded; reason: the source's structured circuits are specified by Hadamard subsets, affine coefficients and block supports
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, Theorem 15, p.72 (PDF p.74), Eq. (346)

import Definitions.Def_DepthOptQC_Synth_Supplement_StructuredFourierCircuit

set_option autoImplicit false

namespace DepthOptQC.Synth.Supplement

open QAlgorithms

/-- **Theorem 15 (Structured Fourier Representations of Standard Circuits)** — Vasconcelos,
arXiv:2609.34659, p.72, Eq. (346). The four wide standard models have structured Fourier
representations over `A,Af,T,Tf` with `O(d+1)` phase layers. The bounded models QUNC, QUNCf and
QNCf have representations over `A3,A3f,A3f` with the additive doubly-logarithmic layer bound.
All representations approximate designated-output acceptance uniformly over inputs and are chosen
independently of the input.

**Formalization Note.** Polynomial costs bound both the concrete syntax description and width.
The two conjuncts preserve every model/family clause and the different depth regimes. -/
theorem theorem_15 :
    ∃ K : ℝ, 0 < K ∧ ∃ k : ℕ,
      (∀ (M : WideModel) (n d s : ℕ) (C : DecisionCircuit (standardWideGateSet M) n),
        2 ≤ s → C.depth = d → C.size ≤ s → C.width ≤ s →
        ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
          ∃ U : StructuredFourierCircuit (widePhaseFamily M) n,
            (U.phases.length : ℝ) ≤ K * (d + 1) ∧
            (U.width : ℝ) ≤ K * ((s : ℝ) + 1 / ε) ^ k ∧
            (U.descriptionLength : ℝ) ≤ K * ((s : ℝ) + 1 / ε) ^ k ∧
            ∀ x : Qubits n, |U.acceptance x - C.acceptance x| ≤ ε) ∧
      (∀ (B : BoundedFourierSource) (n d s : ℕ)
        (C : DecisionCircuit (boundedSourceGateSet B) n),
        2 ≤ s → C.depth = d → C.size ≤ s → C.width ≤ s →
        ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
          ∃ U : StructuredFourierCircuit (boundedSourcePhaseFamily B) n,
            (U.phases.length : ℝ) ≤ K * ((d : ℝ) + loglogScale ((s : ℝ) / ε)) ∧
            (U.width : ℝ) ≤ K * ((s : ℝ) + 1 / ε) ^ k ∧
            (U.descriptionLength : ℝ) ≤ K * ((s : ℝ) + 1 / ε) ^ k ∧
            ∀ x : Qubits n, |U.acceptance x - C.acceptance x| ≤ ε) := by sorry

end DepthOptQC.Synth.Supplement
