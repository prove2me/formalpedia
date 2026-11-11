-- Prove2me | Theorems.Thm_EFI1PRS_Uniform_conditional_aep
-- name    : EFI1PRS.Uniform.conditional_aep
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T05:03:26.558297+00:00
-- url     : https://prove2.me/theorems/7befd241-bf22-48c1-bd68-abf279dc876b
-- title:
--   Fact 2.15 — finite conditional AEP with constant 10
-- statement:
--   Let $A$ be one qubit, $B$ any nonzero finite-dimensional quantum register, and $\zeta_{AB}$ any normalized state. For $0<\delta<1$, set $g(\delta)=-\log_2(1-\sqrt{1-\delta^2})$. For every integer $m$ with $m\ge(8/5)g(\delta)$,
--
--   $$H_{\min}^{\delta}(A^m\mid B^m)_{\zeta^{\otimes m}}\ge mH(A\mid B)_\zeta-10\sqrt{m g(\delta)}.$$
--
--   The constant 10 is independent of the dimension of $B$. Conditional entropy may be negative. The smoothing is over the complete subnormalized purified-distance ball, as specified by the source.
--
--   Differences from the source:
--   - encoding: a supremum of domination exponents, with purified-distance smoothing → EReal suprema, trace-one reference states and the full published subnormalized purified-distance ball; reason: infinite entropy is represented without a junk real supremum or a support restriction
--   - encoding: the conditional AEP formula on the nontrivial purified-distance smoothing range → explicit hypotheses 0 < delta < 1, normalized zeta, and a nonempty finite side register; reason: these make the source state and smoothing conventions explicit; in particular the real logarithm default at delta=0 cannot discharge the AEP premise
-- source:
--   Rishabh Batra, STOC 2027 submission #273 (October 2026), EFI ⇔ 1PRS, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/273.pdf, Fact 2.15, PDF/printed p. 10

import Definitions.Def_EFI1PRS_Uniform_Generator

/-! Rishabh Batra, EFI ⇔ 1PRS, pinned October 2026 STOC submission #273.
Statement-preparation draft; proof is a future solver obligation. -/
noncomputable section
namespace EFI1PRS.Uniform
open QAlgorithms
open scoped BigOperators Matrix ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq

theorem conditional_aep {B : Type*} [Fintype B] [Nonempty B]
    (ζ : Matrix (Bool × B) (Bool × B) ℂ) (hζ : IsDensityMatrix ζ)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (m : ℕ) (hm : (8/5 : ℝ)*aepPenalty δ ≤ (m : ℝ)) :
    ((m : ℝ)*conditionalEntropy ζ - 10*Real.sqrt ((m : ℝ)*aepPenalty δ) : EReal) ≤
      smoothConditionalMin
        (QAlgorithms.Papers.Independent.Intakenext100.P07.paperJointPower ζ m) δ := by sorry

end EFI1PRS.Uniform
