-- Prove2me | Theorems.Thm_AgnGaussTomo_lemma_3_16
-- name    : AgnGaussTomo.lemma_3_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:25:53.728207+00:00
-- url     : https://prove2.me/theorems/2577d4f2-893e-41f4-b76a-d30777085044
-- title:
--   Lemma 3.16 — direct gradient estimation with projective measurements
-- statement:
--   There is a universal constant $C>0$ such that for every $n$, every $\kappa\in(0,1)$ and every $\delta\in(0,1/2)$ there is an adaptive scheme of **single-copy projective measurements** (each round draws a recorded random seed and performs a projective measurement, with finitely many outcomes) using
--
--   $$
--   N\le C\,n^2\kappa^{-2}\log(2/\delta)
--   $$
--
--   copies, and an estimator $\hat g$ with values in $\mathcal P_n$, such that for every $n$-mode state $\sigma$ the objective $f_\sigma$ is differentiable at $0$ and, with probability at least $1-\delta$,
--
--   $$
--   \|\hat g-\nabla f_\sigma(0)\|_{\mathcal P}\le\kappa .
--   $$
--
--   Measuring the gradient at the vacuum directly, rather than by finite differences, is what brings the refinement stage to $\widetilde O(n^2\epsilon^{-1})$ copies.
--
--   Differences from the source:
--   - reading: the O constant → universal constants chosen before n and every other parameter; reason: the paper calls them universal constants; ≲ and O hide absolute constants
--   - reading: we can estimate ∇f_σ(0) to error κ → with probability at least 1 − δ the estimate is within κ of ∇f_σ(0) in ‖·‖_P; reason: δ is the failure probability
--   - reading: single-copy projective measurements → every round draws a classical seed s (recorded with the outcome) and performs a projection-valued measurement, with finitely many seeds and outcomes; reason: the proof's measurement (p. 25): a random s ∈ {±1, ±i}, then the basis {|v_sk⟩⟨v_sk|} ∪ {I − Π}
--   - reading: ∇f_σ(0) (differentiability presupposed) → f_σ is differentiable at 0, and the gradient is Mathlib's gradient on Pspace n; reason: asserting differentiability excludes a junk zero gradient
--   - generalization: there exists an algorithm → an adaptive scheme of seeded projective measurements on a number N of copies fixed in advance, with an estimator that is a function of the transcript, depending on n, κ and δ only; reason: this is one kind of algorithm, so the existence claim specializes to the source's; the scheme depends only on the parameters named in the statement, never on the unknown state
--   - encoding: with probability at least 1 − δ → an inner probability: a measurable set of transcripts of probability ≥ 1 − δ on which the guarantee holds; reason: the guarantee need not define a measurable event; same meaning for measurable events
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), Lemma 3.16, printed p. 24 (PDF p. 27); proof on pp. 25–26

import Mathlib
import Definitions.Def_AgnGaussTomo_Succeeds
import Definitions.Def_AgnGaussTomo_IsSeededProjective
import Definitions.Def_AgnGaussTomo_fobj

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace AgnGaussTomo

/-- **Lemma 3.16 (Direct gradient estimation).** Arulandu, Chen, Chen, Li, Ma, *Finding Gaussian Structure
in Bosonic States*, arXiv:2610.06810 (version of 3 Nov 2026), Lemma 3.16, printed p. 24 (PDF p. 27):
"For any n-mode state σ, κ ∈ (0, 1), and δ ∈ (0, 1/2), we can estimate ∇f_σ(0) to error κ in ‖·‖_P
using O(n² κ^{-2} log(2/δ)) copies and single-copy projective measurements."

**Formalization Note.** The scheme depends on `n, κ, δ` only and works for every state `σ`; "estimate
to error `κ`" is read as "with probability at least `1 − δ`, `‖est − ∇f_σ(0)‖_P ≤ κ`". Each round draws a
classical seed `s` and performs a projective measurement (`IsProjectiveScheme`; seeds and outcomes in
finite sets). The gradient is Mathlib's `gradient` on `Pspace n`, whose inner product is `⟨·,·⟩_{P_n}`;
the statement also asserts that `f_σ` is differentiable at `0`, which rules out a junk zero
gradient. The `O` constant is universal. -/
theorem lemma_3_16 : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (κ δ : ℝ), 0 < κ → κ < 1 → 0 < δ → δ < 1 / 2 →
      ∃ (N a b : ℕ) (S : BosonicLearn.AdaptiveScheme n N (Fin a × Fin b))
        (est : (Fin N → Fin a × Fin b) → Pspace n),
        (N : ℝ) ≤ C * (n : ℝ) ^ 2 / κ ^ 2 * Real.log (2 / δ) ∧
        IsProjectiveScheme S ∧
        ∀ σ : State (Occupation (Fin n)),
          DifferentiableAt ℝ (fobj σ.coefficients) 0 ∧
          Succeeds S σ.coefficients (fun x => ‖est x - gradient (fobj σ.coefficients) 0‖ ≤ κ) δ := by sorry

end AgnGaussTomo
