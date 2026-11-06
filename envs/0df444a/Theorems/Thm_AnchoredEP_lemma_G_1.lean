-- Prove2me | Theorems.Thm_AnchoredEP_lemma_G_1
-- name    : AnchoredEP.lemma_G_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:37:00.173569+00:00
-- url     : https://prove2.me/theorems/5979e604-478c-4691-90c7-9e814f25f6c0
-- title:
--   Lemma G.1 — regularized Taylor model: error bound and maximal monotonicity
-- statement:
--   Let $p\ge2$, let $F:\mathbb R^d\to\mathbb R^d$ be monotone and satisfy Assumption 5.1 with constant $L_p$, and let $\mathbb T^{(p-1)}_\lambda(z';z)=\mathbb T^{(p-1)}(z';z)+\frac{\lambda}{(p-1)!}\|z'-z\|^{p-1}(z'-z)$. Then:
--
--   1. for every $\lambda\ge0$ and all $z,z'\in\mathbb R^d$,
--   $$
--   \big\|F(z')-\mathbb T^{(p-1)}_\lambda(z';z)\big\|\le\frac{L_p+p\lambda}{p!}\,\|z'-z\|^p ;
--   $$
--   2. for every $\lambda\ge L_p$ and every center $z$, the single-valued operator $\mathbb T^{(p-1)}_\lambda(\cdot\,;z)$ is maximal monotone and has domain $\mathbb R^d$.
--
--   The first part bounds the error of the surrogate in the relative-error condition of the AEP framework; the second makes every subproblem of the method uniquely solvable.
--
--   Differences from the source:
--   - encoding: the (p−1)th derivative of F exists and is L_p-Lipschitz (Assumption 5.1) → Assumption51 p L F = ContDiff ℝ (p−1) F ∧ ‖iteratedFDeriv (p−1) F z − iteratedFDeriv (p−1) F z′‖ ≤ L‖z − z′‖; reason: the existence of D^{p−1}F is presupposed by the source; a Lipschitz (p−1)th derivative is continuous, so the same operators qualify
--   - encoding: T_λ(·; z) is maximal monotone and has domain ℝ^d → IsMaximalMonotone (x ↦ {T_λ(x; z)}) ∧ dom (x ↦ {T_λ(x; z)}) = univ; reason: a single-valued operator is the set-valued operator with singleton values
--   - generalization: the paper's standing assumption that Problem (1) has a solution (for some H) → not assumed; reason: the lemma concerns F and its model only; with the assumption added it is the source's statement
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Lemma G.1 ([JM24, Lemma 7.1]), p.36, Eq. (83)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_AnchoredEP_Assumption51
import Definitions.Def_AnchoredEP_regTaylor

open ThreeOpSplitting.Convergence

namespace AnchoredEP

/-- **Lemma G.1 (regularized Taylor model: error bound and maximal monotonicity).** Jiang–Yoon,
*Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems*,
arXiv:2609.30212, Lemma G.1 ([JM24, Lemma 7.1]), p.36: "Under Assumption 5.1, define
`𝕋_λ^{(p−1)}(z′; z) := 𝕋^{(p−1)}(z′; z) + λ/(p − 1)! ‖z′ − z‖^{p−1}(z′ − z)`. For every `λ ≥ 0`,
`‖F(z′) − 𝕋_λ^{(p−1)}(z′; z)‖ ≤ (L_p + pλ)/p! ‖z′ − z‖^p`. (83) Moreover, if `λ ≥ L_p`, then
`𝕋_λ^{(p−1)}(·; z)` is maximal monotone and has domain `ℝ^d`."

Both clauses are stated, for `p ≥ 2` (Section 5) and `F` monotone (the paper's standing
assumption on Problem (1), p.1).

**Formalization Note.** `regTaylor F p lam z z'` is `𝕋_lam^{(p−1)}(z′; z)` (center `z`). The
single-valued model is the set-valued operator `x ↦ {𝕋_lam^{(p−1)}(x; z)}`; monotonicity of `F` is
`IsMonotoneOp (fun x => {F x})`. -/
theorem lemma_G_1 {d : ℕ} (p : ℕ) (hp : 2 ≤ p) (L : ℝ)
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hF : IsMonotoneOp (fun x => ({F x} : Set (EuclideanSpace ℝ (Fin d)))))
    (hA : Assumption51 p L F) :
    (∀ lam : ℝ, 0 ≤ lam → ∀ z z' : EuclideanSpace ℝ (Fin d),
      ‖F z' - regTaylor F p lam z z'‖ ≤ (L + p * lam) / (p.factorial : ℝ) * ‖z' - z‖ ^ p) ∧
    (∀ lam : ℝ, L ≤ lam → ∀ z : EuclideanSpace ℝ (Fin d),
      IsMaximalMonotone (fun x => ({regTaylor F p lam z x} : Set (EuclideanSpace ℝ (Fin d)))) ∧
      dom (fun x => ({regTaylor F p lam z x} : Set (EuclideanSpace ℝ (Fin d)))) = Set.univ) := by sorry

end AnchoredEP
