-- Prove2me | Theorems.Thm_FiniteFields_Betti_complexPoints_isEmbedding_of_isAffineOpen
-- name    : FiniteFields.Betti.complexPoints_isEmbedding_of_isAffineOpen
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-21T08:39:19.82518+00:00
-- url     : https://prove2.me/theorems/f4c1b627-c41a-4261-85ed-0b7c8240c392
-- title:
--   On an affine open $W$, $W(\mathbb C)$ is open in $Y(\mathbb C)$ and carries the weak topology of regular functions
-- statement:
--   Let $R$ be a commutative ring, $\sigma:R\to\mathbb C$ a ring homomorphism and $\pi:Y\to\operatorname{Spec}R$ a scheme over $R$. Its **complex points** along $\sigma$ are the morphisms $x:\operatorname{Spec}\mathbb C\to Y$ with $\pi\circ x=\operatorname{Spec}\sigma$, i.e. the $\mathbb C$-points of the base change $Y\times_{R,\sigma}\mathbb C$; they form the space $Y(\mathbb C)$ with the analytic topology of `FiniteFields_BettiNumbers`.
--
--   Let $W\subseteq Y$ be an affine open subscheme and $W(\mathbb C)\subseteq Y(\mathbb C)$ the set of complex points that factor through $W$. For $t\in\Gamma(Y,W)$ and $x\in W(\mathbb C)$ write $t(x)\in\mathbb C$ for the value of $t$ at $x$. Then:
--
--   1. $W(\mathbb C)$ is open in $Y(\mathbb C)$;
--   2. the map
--   $$W(\mathbb C)\longrightarrow\mathbb C^{\Gamma(Y,W)},\qquad x\longmapsto\bigl(t(x)\bigr)_{t\in\Gamma(Y,W)},$$
--   is a topological embedding, where $\mathbb C^{\Gamma(Y,W)}$ has the product topology.
--
--   Thus the topology of $Y(\mathbb C)$ restricted to an affine open is the weakest one making all regular functions continuous, which justifies calling it the analytic topology. No finiteness assumption on $\pi$ is needed.
--
--   **Formalization Note** $t(x)$ is the image of $t$ under $x^*:\Gamma(Y,W)\to\Gamma(\operatorname{Spec}\mathbb C)\cong\mathbb C$ (`appLE` followed by `Scheme.ΓSpecIso`); $W(\mathbb C)$ is the subtype of points $x$ with $x^{-1}(W)$ equal to $\operatorname{Spec}\mathbb C$.
-- source:
--   J.-P. Serre, *Géométrie algébrique et géométrie analytique*, Ann. Inst. Fourier 6 (1956), 1–42, §2, n° 5, Proposition 2 and the following Remarque (pp. 8–9): the topology of the analytic space associated to X is the coarsest one making the regular functions on the Zariski-open subsets of X continuous. Lean: original formalization for this project (Lean v4.33.1, Mathlib 0df444a), file `Bridge/Betti/ComplexPointsAffine.lean`.

import Mathlib
import Definitions.Def_FiniteFields_BettiNumbers

open AlgebraicGeometry CategoryTheory

theorem FiniteFields.Betti.complexPoints_isEmbedding_of_isAffineOpen {R : Type} [CommRing R] (σ : R →+* ℂ)
    {Y : Scheme.{0}} (π : Y ⟶ Spec (.of R)) (W : Y.Opens) (hW : IsAffineOpen W) :
    IsOpen {x : ComplexPoints σ π | ⊤ ≤ x.1 ⁻¹ᵁ W} ∧
    Topology.IsEmbedding (fun x : {x : ComplexPoints σ π // ⊤ ≤ x.1 ⁻¹ᵁ W} ↦
      fun t : Γ(Y, W) ↦ (Scheme.ΓSpecIso (.of ℂ)).hom (x.1.1.appLE W ⊤ x.2 t)) := by sorry
