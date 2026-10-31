-- Prove2me | Theorems.Thm_CompositeSAA_exists_subadditive_modulus
-- name    : CompositeSAA.exists_subadditive_modulus
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:32:27.879005+00:00
-- url     : https://prove2.me/theorems/fd724251-09d5-42ae-9154-521f65920a53
-- title:
--   Proof of Theorem 4, p.7 — a modulus of continuity on a convex set can be chosen subadditive (and nondecreasing)
-- statement:
--   Let $C$ be a convex subset of a real normed space and let $(G_i)_{i\in\iota}$ be real functions on $C$ that all admit the modulus of continuity $w$:
--
--   $$
--   |G_i(x)-G_i(x')|\le w(\|x-x'\|)\qquad(x,x'\in C,\ i\in\iota).
--   $$
--
--   Then there is a modulus of continuity $\omega$, nondecreasing and subadditive on $[0,\infty)$ ($\omega(s+t)\le\omega(s)+\omega(t)$), that is a common modulus of all $G_i$ on $C$.
--
--   In the proof of Theorem 4(b) this is the first step towards the linear growth bound $|g(x)|\le\alpha\|x\|+b$ for all functions of the class $\tilde{\mathfrak F}$.
--
--   Differences from the source:
--   - generalization: one real-valued function admitting $w$ → a family of functions with a common modulus $w$, and the selected modulus is also nondecreasing; reason: a one-element family is the printed claim, and the extra conclusion only strengthens it.
--   - encoding: "a convex subset of a metric space" → a convex subset of a real normed space; reason: convexity needs a linear structure, and the paper applies it in $\mathbb R^m$.
-- source:
--   Dentcheva, Lin, Penev, arXiv:2201.01338v1, proof of Theorem 4, p.7

import Mathlib
import Definitions.Def_CompositeSAA_IsModulus

namespace CompositeSAA

/-- Dentcheva, Lin, Penev, arXiv:2201.01338v1, proof of Theorem 4, p.7: "if a real-valued function,
which is defined on a convex subset of a metric space, admits a modulus of continuity `w`, then `w`
can be selected to be subadditive."

Stated for a family: if every `G i` admits the modulus `w` on a convex set `C`, then there is a
common modulus `ω` of all `G i` on `C` that is nondecreasing and subadditive on `[0, ∞)`.

**Formalization Note** The "convex subset of a metric space" is a convex subset of a real normed
space. The family version and the monotonicity of `ω` are more than the printed single-function
claim; monotonicity is what the next step of the proof (continuity, p.7) needs. -/
theorem exists_subadditive_modulus {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type*} (C : Set F) (hC : Convex ℝ C) (G : ι → F → ℝ) (w : ℝ → ℝ) (hw : IsModulus w)
    (hG : ∀ i, ∀ x ∈ C, ∀ x' ∈ C, |G i x - G i x'| ≤ w ‖x - x'‖) :
    ∃ ω : ℝ → ℝ, IsModulus ω ∧ MonotoneOn ω (Set.Ici 0) ∧
      (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → ω (s + t) ≤ ω s + ω t) ∧
      ∀ i, ∀ x ∈ C, ∀ x' ∈ C, |G i x - G i x'| ≤ ω ‖x - x'‖ := by sorry

end CompositeSAA
