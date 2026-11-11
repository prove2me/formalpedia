-- Prove2me | Theorems.Thm_ArbLindbladLearn_lemma_4_5
-- name    : ArbLindbladLearn.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:30:00.912367+00:00
-- url     : https://prove2.me/theorems/6557de51-bd30-48c8-9dfd-5805d5046740
-- title:
--   Lemma 4.5 — unbiased shadow estimator with second moment $\le160$
-- statement:
--   Fix $t\ge0$ and the random Clifford probing experiment of Lemma 4.4. Let $A$ be a normalized operator, $\frac1d\mathrm{tr}(A^\dagger A)=1$, with $\|A\|_\infty\le\sqrt2$, and let $X_A=\mathrm{tr}(\Pi_A\hat J_t)$ be the single-snapshot estimator. Then
--   $$\mathbb E[X_A]=f_A(t),\qquad\mathbb E[X_A^2]\le160 .$$
--
--   The dimension-free second moment is what makes the experiment count independent of $n$.
--
--   Differences from the source:
--   - encoding: a Lindbladian ℒ of the form (8) with h_a ∈ ℝ and γ Hermitian PSD → coefficients c = (h, γ) with IsLindbladCoeffs c and the generator gen c; reason: ℒ is determined by its coefficients (Lemma 3.1) and every such coefficient vector gives a Lindbladian; same instances
--   - reading: φ = C†|b⟩⟨b|C for a uniformly random Clifford C and Born outcome b → the outcome law of eq. (29); reason: as in Lemma 4.4
--   - encoding: X_A = tr(Π_A Ĵ_t) and f_A(t) → their real parts; reason: both are real
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Lemma 4.5, p.29

import Mathlib
import Definitions.Def_ArbLindbladLearn_snapshot
import Definitions.Def_ArbLindbladLearn_signal
import Definitions.Def_ArbLindbladLearn_opNorm
import Definitions.Def_ArbLindbladLearn_IsLindbladCoeffs

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- Lemma 4.5 (Unbiased shadow estimator with constant second moment; Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…),
p.29). Let `A` be a normalized operator (`(1/d)tr(A†A) = 1`) with `‖A‖_∞ ≤ √2`, and let
`X_A = tr(Π_A Ĵ_t)` be the single-snapshot estimator. Then `E[X_A] = f_A(t)` and `E[X_A²] ≤ 160`.

**Formalization Note** The recorded pair `(ψ, φ)` has the law `shadowWeight`: `ψ` uniform on `Stab_n`, then `φ ∈ Stab_n`
with probability `d·tr(e^{tℒ}(ψ)φ)/|Stab_n|` (eq. (29), p.28), the law of `φ = C†|b⟩⟨b|C` for a
uniformly random Clifford `C` and the computational-basis outcome `b`. `t ≥ 0` is fixed (p.28). `X_A = ⟨Φ_A|Ĵ_t|Φ_A⟩` (`snapEst`) and
`f_A(t) = ⟨Φ_A|J_t|Φ_A⟩` (`witnessSignal`) are real. Every `n` is covered. -/
theorem lemma_4_5 {n : ℕ} (c : Coeffs n) (hc : IsLindbladCoeffs c) (t : ℝ) (ht : 0 ≤ t)
    (A : Op (Qubits n)) (hA : (Aᴴ * A).trace / (2 : ℂ) ^ n = 1)
    (hA2 : opNorm A ≤ Real.sqrt 2) :
    shadowExpect c t (fun ψ φ => snapEst A ψ φ) = witnessSignal c A t ∧
      shadowExpect c t (fun ψ φ => snapEst A ψ φ ^ 2) ≤ 160 := by sorry

end ArbLindbladLearn
