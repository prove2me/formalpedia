-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_exists_pt_eq_map_and_toOmega_eq_of_algEquiv
-- name    : CerednikDrinfeld.FormalOmega.AdicPoint.exists_pt_eq_map_and_toOmega_eq_of_algEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/81186bc3-4425-5ee2-a03e-1bac0d150be4
-- title:
--   Transport of an adic point along a base automorphism
-- statement:
--   Let $\mathcal O$ be a commutative ring, $K_0$ a field that is an $\mathcal O$-algebra, $\pi \in \mathcal O$, let $R$ be an $\mathcal O$-algebra and $C$ a field that is an $R$-algebra. Let $\tau$ be an $\mathcal O$-algebra automorphism of $R$ and $s$ a ring automorphism of $C$ with $\tau$ lying under $s$, i.e. $\tau(a)$ and $s(a)$ have the same image in $C$ for every $a \in R$. Let $\tau_k$, for $k \in \mathbb N$, be $\mathcal O$-algebra endomorphisms of $R/(\pi^{k+1})$ (the image of $\pi$ in $R$ being raised to the power $k+1$) that are compatible with $\tau$, in the sense that $\tau_k$ applied to the class of $a \in R$ is the class of $\tau(a)$. Let $x$ be an adic point of the formal upper half plane over $R$: a family $x_k$ of Deligne data over $R/(\pi^{k+1})$ — for each full $\mathcal O$-lattice $M$ in $K_0^2$ a submodule $\mathrm{line}(M)$ of $(R/(\pi^{k+1})) \otimes_{\mathcal O} M$ with invertible quotient, monotone in $M$, equivariant for scalar homotheties, and non-degenerate at every prime of $R/(\pi^{k+1})$ — compatible under base change along the transition maps $R/(\pi^{k+2}) \to R/(\pi^{k+1})$. Then there exists an adic point $x'$ over $R$ with $x'_k$ equal, for every $k$, to the base change of $x_k$ along $\tau_k$ (each line being replaced by the span of its image under $\tau_k \otimes \mathrm{id}$), and whose canonical coordinate satisfies $\mathrm{toOmega}_C(x') = s(\mathrm{toOmega}_C(x))$; here $\mathrm{toOmega}_C(y)$ is the unique $z \in C$ with $(z,1)$ in the $C$-span of the image in $C^2$ of the standard line of $y$, when such a $z$ exists and is unique, and $0$ otherwise.
--
--   This records the functoriality of Drinfeld's formal upper half plane in the test algebra, in the form of Galois transport: an automorphism of the base ring carries an adic point to an adic point and acts on its canonical coordinate through the induced automorphism of the residue field. It is used in the study of germs of functions on a Čerednik–Drinfeld quotient under an isometric automorphism, where $R$ is the valuation ring of $C$ and $\tau$ the restriction of $s$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_AdicPoint_exists_pt_eq_map_and_toOmega_eq_of_algEquiv.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.AdicPoint.exists_pt_eq_map_and_toOmega_eq_of_algEquiv
    {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] (π : 𝒪)
    {R : Type} [CommRing R] [Algebra 𝒪 R] (C : Type) [Field C] [Algebra R C]
    (τ : R ≃ₐ[𝒪] R) (s : C ≃+* C) (hτs : ∀ a : R, algebraMap R C (τ a) = s (algebraMap R C a))
    (τn : ∀ k : ℕ, modPow π R k →ₐ[𝒪] modPow π R k)
    (hτn : ∀ (k : ℕ) (a : R), τn k (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (k + 1)}) a) =
      Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (k + 1)}) (τ a))
    (x : AdicPoint K₀ π R) :
    ∃ x' : AdicPoint K₀ π R, (∀ k : ℕ, x'.pt k = DeligneDatum.map π (τn k) (x.pt k)) ∧
      x'.toOmega C = s (x.toOmega C) := by sorry
