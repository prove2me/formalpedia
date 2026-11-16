-- Prove2me | Theorems.Thm_AgnHalfMem_Supplement_theorem_5_1
-- name    : AgnHalfMem.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:58:19.250201+00:00
-- url     : https://prove2.me/theorems/29677a4f-f28e-4479-b739-fa46660cfd65
-- title:
--   Theorem 5.1 (corrected: memory $O(d\log(2/\gamma)+\log(1/\varepsilon))$, $0<\varepsilon<1$) — realizable $\gamma$-margin halfspaces are learnable with $O(1/(\gamma^2\varepsilon))$ samples
-- statement:
--   There is a constant $C>0$ such that for every dimension $d$, every $0<\varepsilon<1$ and every $0<\gamma\le1$ there is a private-coin streaming algorithm with at most
--   $$
--   2^{\,C\,(d\log_2(2/\gamma)+\log_2(1/\varepsilon))}\ \text{memory states}\qquad\text{and at most}\qquad \frac{C}{\gamma^2\varepsilon}\ \text{samples}
--   $$
--   with the following property. For every distribution $D$ on $\mathbb R^d\times\{-1,1\}$ that is linearly separable with a $\gamma$-margin, run on i.i.d. samples from $D$, it outputs with probability at least $2/3$ a homogeneous halfspace $x\mapsto\mathrm{sign}(\langle w,x\rangle)$ with $\|w\|_2=1$ whose misclassification error $\Pr_{(x,y)\sim D}[\mathrm{sign}(\langle w,x\rangle)\ne y]$ is at most $\varepsilon$.
--
--   The algorithm may depend on $d$, $\varepsilon$ and $\gamma$ but not on $D$. Its memory, $O(d\log(2/\gamma)+\log(1/\varepsilon))$ bits, includes every random choice it keeps. This shows that the agnostic memory lower bounds (Theorems 4.3 and 4.10) are not artifacts of the precision needed to represent a halfspace.
--
--   **Formalization Note** The algorithm is a deterministic measurable branching program that reads a fresh private coin $u\sim\mathrm{Unif}[0,1]$ with each sample. Memory of $b$ bits means at most $2^b$ states, and $O(\cdot)$ is one explicit constant $C$ chosen before $d,\varepsilon,\gamma$.
--
--   Differences from the source:
--   - correction: memory O(d log(1/γ) + log(1/ε)) → card S ≤ 2^{C(d·log₂(2/γ) + log₂(1/ε))}; reason: the printed bound is false at γ = 1 for large d: a program with |S| states and T samples has at most (T+1)|S| leaf halfspaces, a number independent of d under the printed bounds, so for d larger a unit w* orthogonal to all of them and D uniform on {(w*,+1), (−w*,−1)} (margin exactly 1) gives every output error 1/2; the paper's own introduction (p.3) and proof (pp.26, 28) use log(2/γ)
--   - correction: ε > 0 → 0 < ε < 1; reason: for ε larger than (2/γ)^d the bound C(d log(2/γ) + log(1/ε)) is negative and no program (which has at least one state) meets it, so the statement is false there; for ε ≥ 1 every output has error ≤ 1 ≤ ε, so PAC learning is about ε < 1
--   - reading: "a distribution linearly separable with a γ-margin" → IsMarginSeparable D γ: a unit w* with x ≠ 0 and sgn(y)⟨w*,x⟩ ≥ γ‖x‖₂ D-almost surely; reason: p.26 normalizes the samples to ‖x‖₂ ≤ 1, y⟨w*,x⟩ ≥ γ, which needs x ≠ 0; an atom at 0 labelled −1 would otherwise make the theorem false
--   - encoding: "PAC learning algorithm" with its own randomness (Algorithm 1 stores J) → a deterministic measurable branching program BP S ((Fin d → ℝ) × ℝ) T fed ((x,u),y) with a fresh coin u ∼ Unif[0,1] per sample; output = leaf label read at coin 0; reason: private randomness counted in memory, as in the paper's memory count; a public seed would be free memory
--   - encoding: O(·) bounds, bits → one constant C chosen before d, ε, γ; card S ≤ 2^b for b bits; log base 2; algorithm chosen after d, ε, γ and before D; reason: Lean conventions; base changes of log are absorbed in C
--   - encoding: "outputs a halfspace" → the output classifier lies in H_d (x ↦ sign⟨w,x⟩, Σ wᵢ² = 1, sign(0) = +1); reason: the paper's halfspaces are homogeneous (p.2); sign⟨w,·⟩ for w ≠ 0 equals that of w/‖w‖₂
--   - encoding: d ≥ 1 implicit → every d : ℕ; reason: at d = 0 there is no unit vector, so no distribution is separable and the case is vacuous
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), Theorem 5.1, p.19 (proof App. A.2, pp.25–28; memory term as on pp.3, 26, 28)

import Mathlib
import Definitions.Def_AgnHalfMem_halfspace
import Definitions.Def_AgnHalfMem_err
import Definitions.Def_AgnHalfMem_BP
import Definitions.Def_AgnHalfMem_Supplement_coinStream
import Definitions.Def_AgnHalfMem_Supplement_IsMarginSeparable

open MeasureTheory

namespace AgnHalfMem

namespace Supplement

/-- **Theorem 5.1 (upper bound in the realizable case), corrected memory term.** S. Garg,
T. Jadhav, *Memory-Sample Tradeoffs for Agnostically Learning Halfspaces*, STOC 2027 submission
(manuscript, PDF sha256 386bc9b3…43f84d5), Theorem 5.1, p.19: "There exists a PAC learning
algorithm such that, for any ε > 0, 0 < γ ≤ 1, given a stream of samples drawn from a
distribution linearly separable with a γ-margin, the algorithm uses O(d log(1/γ) + log(1/ε)) bits
of memory and O(1/(γ²ε)) samples, and with probability at least 2/3 outputs a halfspace with
misclassification error at most ε." Proof: App. A.2, pp.25–28.

There is a constant `C > 0` such that for every `d`, every `0 < ε < 1` and every `0 < γ ≤ 1`
there is a measurable private-coin streaming algorithm with at most
`2^{C(d log₂(2/γ) + log₂(1/ε))}` memory states and at most `C/(γ²ε)` samples which, on every
distribution `D` linearly separable with a γ-margin, outputs with probability at least `2/3` a
homogeneous halfspace (an element of `H_d`) with misclassification error at most `ε`.

**Formalization Note.** Corrected as in the introduction (p.3) and the proof (pp.26, 28): the
memory term is `d log(2/γ)`, not the printed `d log(1/γ)`, which is false at `γ = 1` for large
`d`; and `ε < 1` (for `ε ≥ 1` every output qualifies, and the printed bound can be negative).
The algorithm may depend on `d, ε, γ` but not on `D`. Its randomness is one fresh coin
`u ∼ Unif[0,1]` per sample, private and kept only through its state (`coinStream`, `pcOutput`).
`O(·)` is one explicit constant `C`; memory of `b` bits is `Fintype.card S ≤ 2^b`. -/
theorem theorem_5_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (ε γ : ℝ), 0 < ε → ε < 1 → 0 < γ → γ ≤ 1 →
      ∃ (S : Type) (_ : Fintype S) (T : ℕ) (b : BP S ((Fin d → ℝ) × ℝ) T),
        b.IsMeasurableBP ∧
        (Fintype.card S : ℝ) ≤ (2 : ℝ) ^ (C * (d * Real.logb 2 (2 / γ) + Real.logb 2 (1 / ε))) ∧
        (T : ℝ) ≤ C / (γ ^ 2 * ε) ∧
        ∀ D : Measure ((Fin d → ℝ) × Bool), IsProbabilityMeasure D → IsMarginSeparable D γ →
          ENNReal.ofReal (2 / 3) ≤
            (Measure.pi fun _ : Fin T => coinStream D)
              {s | pcOutput b s ∈ halfspaces d ∧ err D (pcOutput b s) ≤ ε} := by sorry

end Supplement

end AgnHalfMem
