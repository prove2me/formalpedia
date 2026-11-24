-- Prove2me | Theorems.Thm_EkelandVP_Constraints_Supplement_palais_smale_counterexample
-- name    : EkelandVP.Constraints.Supplement.palais_smale_counterexample
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:26:35.907991+00:00
-- url     : https://prove2.me/theorems/8fa6ba20-4969-4b16-a8ac-a2f23dbe8a23
-- title:
--   Palais–Smale Existence Theorem (corrected: counterexample to the printed claim on a disconnected complete manifold)
-- statement:
--   The printed existence theorem is false on the disconnected domain permitted by §5's within-component metric convention. There exist a complete strong smooth Riemannian Hilbert manifold $M$, a homeomorphism $e:M\to\mathbb N$ with the discrete topology, and a real $C^1$ function $F$ for which
--   $$
--   F(x)=\frac1{e(x)+1}>0,\qquad \|dF_x\|_*=0,\qquad
--   \inf_{x\in M}F(x)=0,
--   $$
--   $$
--   F\text{ satisfies the printed condition (C)},\qquad
--   \neg\exists x\in M\;\forall y\in M,\ F(x)\le F(y).
--   $$
--   The construction uses a countable disjoint union of points, a smooth manifold modeled on the zero Hilbert space, with intrinsic extended distance $+\infty$ between distinct components. Each function is locally constant, so every point is critical. Condition (C) supplies a point of a nonempty set's closure, while the positive values $1/(n+1)$ never attain their lower bound zero. A positive-dimensional version uses a disjoint union of copies of $\mathbb R$ with the same component values.
--
--   **Formalization Note** The Lean statement includes existence of the complete Riemannian geometry and smoothness, not just a scalar sequence. DISPROOF.md retains the p.340 statement, the p.341 closure-to-cluster inference, and the distinction between a globally finite intrinsic metric and the within-component convention. This item is the refutation of the printed claim on disconnected manifolds; the corrected existence statement, attainment on every connected component (equal to the printed claim on connected manifolds), is the separate item `palais_smale_existence`.
--
--   Differences from the source:
--   - correction: a bounded-below C¹ function satisfying literal subset condition (C) always attains its infimum on the complete Riemannian manifold → there exists a complete disconnected strong Riemannian Hilbert manifold with a C¹ function satisfying every listed analytic premise and having unattained infimum zero; reason: p.341 incorrectly infers a cluster point from a critical point in the closure of a sequence range; countably many constant components refute that inference and the disconnected assertion, as documented in DISPROOF.md
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), p. 340, Palais–Smale Existence Theorem (PDF 17); https://doi.org/10.1016/0022-247X(74)90025-0

import Mathlib
import Definitions.Def_EkelandVP_Constraints_Supplement_riemannianManifold
import Definitions.Def_EkelandVP_Constraints_Supplement_conditionC
set_option autoImplicit false

open Manifold Bundle
open scoped ContDiff Bundle

namespace EkelandVP.Constraints.Supplement

/-- Counterexample on the full printed domain: a countable disjoint union of points.
A compatible intrinsic extended metric has distance +∞ between distinct components. -/
theorem palais_smale_counterexample :
    ∃ (D : CompleteStrongRiemannian.{0}) (e : D.M ≃ₜ ℕ) (F : D.M → ℝ),
      (∀ x, F x = componentValue (e x)) ∧
      ContMDiff 𝓘(ℝ, D.H) 𝓘(ℝ) 1 F ∧
      (∀ x, differentialNorm D F x = 0) ∧
      ConditionC F (differentialNorm D F) ∧
      (∀ x, 0 < F x) ∧ IsGLB (Set.range F) 0 ∧
      ¬ (∃ x, ∀ y, F x ≤ F y) := by sorry

end EkelandVP.Constraints.Supplement
