-- Prove2me | Theorems.Thm_DetTerminalEmbedding1373_Real_deterministic_signing
-- name    : DetTerminalEmbedding1373.Real.deterministic_signing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:28:11.886107+00:00
-- url     : https://prove2.me/theorems/6c01feb8-6154-4693-8884-7c76b9cdbb58
-- title:
--   Lemma 4.1 — deterministic signing with unequal tolerances
-- statement:
--   There is one deterministic admissible signing program and one universal constant $C=100000$. Given unit vectors $v_j\in E_d$, $0<\delta_j\le1$, and a row count $m$ satisfying $\sum_j2e^{-m\delta_j^2/8}<1/2$, its actual execution halts and outputs $\Sigma\in\{\pm1\}^{m\times d}$. For $A=\Sigma/\sqrt m$,
--
--   $$|\|Av_j\|^2-1|<\delta_j\quad(j\in[L]),\qquad t\le C\,mdL\quad(L>0).$$
--
--   The count $t$ is the executed instruction count. For arbitrary list sizes it also satisfies $t\le C[1+(m+1)(d+1)(L+1)]$, explicitly accounting for empty lists. The same code evaluates the maintained scalar row factors and fixes every sign; no norm certificate or runtime bound is an input. This is the algorithmic signing result used in the preprocessing phase.
--
--   Differences from the source:
--   - encoding: Euclidean spaces and finite indexed vectors or signs → EuclideanSpace over Fin indices and Boolean signs; reason: the Euclidean norm and every real coordinate are retained, with +1 represented by true
--   - encoding: an O(mdL) arithmetic-operation construction → the explicit finite signing program, with a universal charged-instruction constant C=100000; reason: counting scalar instructions, memory access and loop/address work gives this numerical envelope; the derivation is recorded in MODERATION_NOTES.md
--   - reading: the asymptotic O(mdL) construction on a test list → the same bound for nonempty lists, plus C[1+(m+1)(d+1)(L+1)] including empty-list overhead; reason: empty lists have no tests but initialization and writing a sign matrix still cost work; this leaves every nonempty source instance unchanged
-- source:
--   Vladimir Braverman, Kuan Cheng, Jiaqing Zhu, STOC 2027 submission #1373 (October 2026), pp. 12, 15–18, Lemma 4.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1373.pdf

import Definitions.Def_DetTerminalEmbedding1373_Real_execution

set_option autoImplicit false
open scoped ENNReal

namespace DetTerminalEmbedding1373.Real

/-- Lemma 4.1, pp. 12, 15–18. The concrete 746-instruction program evaluates
(27)–(32), not a Gaussian integral oracle. Empty lists retain initialization
and matrix-writing costs; nonempty lists have the source's O(mdL) bound. -/
theorem deterministic_signing :
    ∃ C : ℕ, C = 100000 ∧ Admissible signingProgram ∧
    ∀ (L m d : ℕ) (v : Fin L → E d) (δ : Fin L → ℝ),
      (∀ j, ‖v j‖ = 1) → (∀ j, 0 < δ j ∧ δ j ≤ 1) → TestBudget m δ →
      let s := signingInput m v δ
      let t := haltTime signingProgram s
      Halts signingProgram s t ∧
      t ≤ C * (1 + (m + 1) * (d + 1) * (L + 1)) ∧
      (0 < L → t ≤ C * m * d * L) ∧
      (∀ i j, computedSignMatrix m v δ i j = 1 ∨ computedSignMatrix m v δ i j = -1) ∧
      computedProjection m v δ = Matrix.toEuclideanLin
        (fun i j => computedSignMatrix m v δ i j / Real.sqrt (m : ℝ)) ∧
      (∀ j, |‖computedProjection m v δ (v j)‖ ^ 2 - 1| < δ j) := by sorry

end DetTerminalEmbedding1373.Real
