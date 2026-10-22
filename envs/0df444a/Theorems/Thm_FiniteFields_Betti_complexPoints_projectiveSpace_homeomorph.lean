-- Prove2me | Theorems.Thm_FiniteFields_Betti_complexPoints_projectiveSpace_homeomorph
-- name    : FiniteFields.Betti.complexPoints_projectiveSpace_homeomorph
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-21T08:40:20.64851+00:00
-- url     : https://prove2.me/theorems/85518c82-d807-426a-b609-66571b290245
-- title:
--   The complex points of $\mathbb P^n_R$ are homeomorphic to $\mathbb CP^n$
-- statement:
--   Let $R$ be a commutative ring, $\sigma:R\to\mathbb C$ a ring homomorphism and $n\ge 0$. Let $\mathbb P^n_R=\operatorname{Proj}R[x_0,\dots,x_n]$ with its structure morphism to $\operatorname{Spec}R$, and let $\mathbb P^n_R(\mathbb C)$ be its space of complex points along $\sigma$, with the analytic topology. Then there is a homeomorphism
--   $$\mathbb P^n_R(\mathbb C)\ \cong\ \mathbb CP^n=\bigl(\mathbb C^{n+1}\setminus\{0\}\bigr)/\mathbb C^\times,$$
--   where $\mathbb CP^n$ carries the quotient topology.
--
--   This identifies the analytic topology of `FiniteFields_BettiNumbers` with the usual topology in the basic example, so that the homology of $\mathbb CP^n$ computed in algebraic topology gives the Betti numbers of $\mathbb P^n$.
--
--   **Formalization Note** $\mathbb CP^n$ is `Hatcher.CP n` (definition `Hatcher_ComplexProjectiveSpace`); the statement asserts the existence (`Nonempty`) of a homeomorphism.
-- source:
--   J.-P. Serre, *Géométrie algébrique et géométrie analytique*, Ann. Inst. Fourier 6 (1956), 1–42, §2, n° 5, Proposition 2 and the following Remarque (pp. 8–9): the topology of the analytic space associated to X is the coarsest one making the regular functions on the Zariski-open subsets of X continuous; A. Hatcher, *Algebraic Topology*, Example 0.6 for $\mathbb CP^n$. Lean: original formalization for this project (Lean v4.33.1, Mathlib 0df444a), file `Bridge/Betti/ComplexPointsProj.lean`.

import Mathlib
import Definitions.Def_FiniteFields_BettiNumbers
import Definitions.Def_Hatcher_ComplexProjectiveSpace

open AlgebraicGeometry CategoryTheory

theorem FiniteFields.Betti.complexPoints_projectiveSpace_homeomorph (R : Type) [CommRing R] (σ : R →+* ℂ) (n : ℕ) :
    Nonempty (ComplexPoints σ (projectiveSpaceOver.toSpec R n) ≃ₜ Hatcher.CP n) := by sorry
