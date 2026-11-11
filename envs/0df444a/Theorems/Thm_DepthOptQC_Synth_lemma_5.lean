-- Prove2me | Theorems.Thm_DepthOptQC_Synth_lemma_5
-- name    : DepthOptQC.Synth.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:17:12.759487+00:00
-- url     : https://prove2.me/theorems/045e7db7-8d9d-473d-855a-ee71d170a151
-- title:
--   Lemma 5 — robust amplification of an approximate $\tfrac12R_z(\theta)$ block: errors $\tfrac{13}4\delta$, $\sqrt{13}\,\delta\le5\delta$, leakage $13\delta^2$
-- statement:
--   Let $\theta\in\mathbb R$, $\delta\in[0,1/8]$, and let $W_z$ be a unitary on an ancilla register $A$ and one system qubit whose distinguished block is
--   $$
--   \mathcal B(W_z)=B_z:=\begin{pmatrix}\bar z&0\\0&z\end{pmatrix},\qquad \Big|z-\tfrac12e^{i\theta/2}\Big|\le\delta .
--   $$
--   Then the fixed phase $\varphi=\pi$ satisfies
--   $$
--   \big\|\mathcal B(\mathrm{Amp}(W_z))+R_z(\theta)\big\|\le\tfrac{13}{4}\delta,\qquad
--   \big\|\mathrm{Amp}(W_z)V_0+V_0R_z(\theta)\big\|_{\mathrm{op}}\le\sqrt{13}\,\delta\le5\delta .
--   $$
--   Moreover, for every unit input $|\psi\rangle$, the squared norm of the component of $\mathrm{Amp}(W_z)V_0|\psi\rangle$ outside the all-zero ancilla subspace is at most $13\delta^2$:
--   $$
--   \big\|(I-\Pi)\,\mathrm{Amp}(W_z)V_0|\psi\rangle\big\|^2\le 13\delta^2 .
--   $$
--
--   One step of oblivious amplitude amplification therefore turns the approximate block encoding of $\frac12R_z(\theta)$ into a clean approximation of $-R_z(\theta)$, with error linear in $\delta$ and the same phase for every input.
--
--   **Formalization Note** The system qubit is indexed by `Bool`, with $\bar z$ in the $|0\rangle$ entry. The ancilla register is any finite type with a distinguished point. Both norms are the operator norm.
--
--   Differences from the source:
--   - generalization: A an a-qubit ancilla register with zero state 0^a → any finite type A with a point a₀; reason: the statement and its proof only use V₀, Π and unitarity; the paper's register is the instance A = {0,1}^a
--   - reading: ‖B(Amp(W_z)) + R_z(θ)‖ (norm not labelled in (64)) → operator norm (specNorm); reason: (65) labels the operator norm, and the proof (71) bounds the entries of a diagonal 2×2 matrix, which is its operator norm
--   - encoding: for every unit input, the squared norm of the component outside the all-zero ancilla subspace → ∀ ψ with ‖ψ‖ = 1, ‖(I − Π)·Amp(W_z)·V₀ψ‖² ≤ 13δ²; reason: that component is the image under I − Π of the output, Eq. (76)
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, Lemma 5, pp.21–22

import Definitions.Def_DepthOptQC_Synth_amp
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_ShendeQSD_Synthesis_rz

namespace DepthOptQC.Synth

open QAlgorithms

/-- **Lemma 5 (Robust amplification of an approximate `½R_z(θ)` block)** (Vasconcelos,
*Depth-Optimal Quantum Compilation*, arXiv:2609.34659, Lemma 5, pp.21–22). Let `θ ∈ ℝ`,
`δ ∈ [0, 1/8]`, and let `W_z` be a unitary with distinguished block
`B(W_z) = B_z := diag(z̄, z)`, `|z − ½e^{iθ/2}| ≤ δ` (63). Then the fixed phase `φ = π` satisfies
`‖B(Amp(W_z)) + R_z(θ)‖ ≤ (13/4)δ` (64) and `‖Amp(W_z)V₀ + V₀R_z(θ)‖_op ≤ √13 δ ≤ 5δ` (65), and
for every unit input the squared norm of the component outside the all-zero ancilla subspace is at
most `13δ²`.

**Formalization Note.** The system is one qubit (`Bool`, `false` = `|0⟩`, so `z̄` is the `false`
entry); the ancilla register is any finite type `A` with zero point `a₀`. Both norms are the
operator norm `QAlgorithms.specNorm`; `R_z(θ)` is the published `ShendeQSD.Synthesis.rz`. The leakage of the unit input `ψ` is
`‖(I − Π) Amp(W_z) V₀ ψ‖²`. -/
theorem lemma_5 {A : Type*} [Fintype A] [DecidableEq A] (a₀ : A) (θ δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1 / 8) (W : Matrix (A × Bool) (A × Bool) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (A × Bool) ℂ) (z : ℂ)
    (hB : block a₀ W = Matrix.diagonal fun b => if b then z else (starRingEnd ℂ) z)
    (hz : ‖z - Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) / 2‖ ≤ δ) :
    specNorm (block a₀ (amp a₀ W) + ShendeQSD.Synthesis.rz θ) ≤ 13 / 4 * δ ∧
    specNorm (amp a₀ W * V0 (Sy := Bool) a₀ + V0 (Sy := Bool) a₀ * ShendeQSD.Synthesis.rz θ) ≤
      Real.sqrt 13 * δ ∧
    Real.sqrt 13 * δ ≤ 5 * δ ∧
    ∀ ψ : EuclideanSpace ℂ Bool, ‖ψ‖ = 1 →
      ‖(WithLp.toLp 2 (Matrix.mulVec
          (((1 : Matrix (A × Bool) (A × Bool) ℂ) - proj (Sy := Bool) a₀) * amp a₀ W *
            V0 (Sy := Bool) a₀) (WithLp.ofLp ψ)) : EuclideanSpace ℂ (A × Bool))‖ ^ 2 ≤
        13 * δ ^ 2 := by sorry

end DepthOptQC.Synth
