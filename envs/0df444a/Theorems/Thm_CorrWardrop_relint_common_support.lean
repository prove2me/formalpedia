-- Prove2me | Theorems.Thm_CorrWardrop_relint_common_support
-- name    : CorrWardrop.relint_common_support
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:29:31.544982+00:00
-- url     : https://prove2.me/theorems/18b061f6-a834-4cb5-b700-2db10ec5c729
-- title:
--   Proof of Proposition 4, p.20 — all flows in the relative interior of $\mathrm{WE}(\Gamma)$ have the common support $\times_k B^k$
-- statement:
--   Let $\Gamma$ be a nonatomic game with a convex potential (as in Lemma 3), and let $\operatorname{ri}\mathrm{WE}(\Gamma)$ be the relative interior of the set of Wardrop equilibria in $\mathbb R^{\sqcup_k\mathcal A^k}$. Then for each population $k$ there is a set of actions $B^k\subseteq\mathcal A^k$ such that
--
--   1. every $y\in\operatorname{ri}\mathrm{WE}(\Gamma)$ has support $\{a\in\mathcal A^k: y^k_a>0\}=B^k$ for every $k$, i.e. $\times_k B^k$ is the support of all flows in the relative interior;
--   2. $B^k=\{a\in\mathcal A^k:\ w^k_a>0 \text{ for some } w\in\mathrm{WE}(\Gamma)\}$: whenever $y^k_a>0$ for some WE, this holds at every point of the relative interior.
--
--   This common support is where the KKT multipliers force equal partial derivatives of $\Phi$ at all points of the relative interior.
--
--   Differences from the source:
--   - reading: "has a convex potential" (Definition 5: Φ C¹ on an open neighbourhood Ŷ of Y) → HasConvexPotential Γ Φ, i.e. Φ C¹ and convex on some open convex U ⊇ Y with ∂Φ/∂y^k_a = c^k_a on Y; reason: literal reading of "Φ convex" on its domain; any open neighbourhood of the compact convex Y contains an open convex one
--   - encoding: relative interior of WE(Γ); ×_k B^k is the support → intrinsicInterior ℝ of the image of WE(Γ) in the flow space; for every k, {a | 0 < y k a} = B k; reason: Mathlib's relative interior; the support of a flow profile as one set per population
-- source:
--   Koessler–Scarsini–Tomala, Correlated Equilibria in Large Anonymous Bayesian Games, arXiv:2107.06312v4, proof of Proposition 4, first paragraph of p.20

import Mathlib
import Definitions.Def_CorrWardrop_Model
import Definitions.Def_CorrWardrop_Lagrangian
open MeasureTheory

namespace CorrWardrop

/-- Proof of Proposition 4, common support of the relative interior: if `Γ` has a convex
potential, then for each `k ∈ K` there is a subset of actions `B^k ⊆ A^k` such that `×_k B^k`
is the support of every flow in the relative interior of `WE(Γ)`; moreover `a ∈ B^k` exactly
when `y^k_a > 0` for some WE `y` ("whenever `y^k_a > 0` for some WE, this must be true for all
points in the relative interior of WE").

Koessler–Scarsini–Tomala, arXiv:2107.06312v4, proof of Proposition 4, p.20. -/
theorem relint_common_support {K : Type*} [Fintype K] {A : K → Type*} [∀ k, Fintype (A k)]
    [DecidableEq K] [∀ k, DecidableEq (A k)]
    (Γ : NonatomicGame K A) (Φ : Flow A → ℝ) (hΦ : HasConvexPotential Γ Φ) :
    ∃ B : (k : K) → Set (A k),
      (∀ y ∈ relintWE Γ, ∀ k, support y k = B k) ∧
      ∀ k, B k = {a | ∃ w ∈ WE Γ, 0 < (w : Flow A) k a} := by sorry

end CorrWardrop
