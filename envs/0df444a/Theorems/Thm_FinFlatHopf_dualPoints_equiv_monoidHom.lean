-- Prove2me | Theorems.Thm_FinFlatHopf_dualPoints_equiv_monoidHom
-- name    : FinFlatHopf.dualPoints_equiv_monoidHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/eee937b2-0831-58e3-aac3-30924380a082
-- title:
--   Points of the Cartier dual as characters of the points
-- statement:
--   Let $B$ be a commutative ring and $H$ a commutative Hopf algebra over $B$ whose comultiplication is cocommutative and which is finite and free as a $B$-module, and let $\Omega$ be a field equipped with a $B$-algebra structure. Write $\mathrm{CartierDual}\,B\,H$ for the $B$-linear dual $\mathrm{Module.Dual}\,B\,H$ carrying its Hopf algebra structure, with [`CartierDual.ofDual`](def/HopfAlgebra_CartierDual.html#L956) the $B$-linear identification of $\mathrm{Module.Dual}\,B\,H$ with it, and write `WithConv` for the type synonym carrying the convolution monoid structure on a set of $B$-algebra maps into $\Omega$, with `WithConv.ofConv` and `WithConv.toConv` the underlying bijections. Assume that the convolution monoid $\mathrm{WithConv}(H \to_{\mathrm{alg}[B]} \Omega)$ is finite of cardinality exactly $\mathrm{finrank}_B H$. Then there exists an isomorphism of monoids $e$ from $\mathrm{WithConv}(\mathrm{CartierDual}\,B\,H \to_{\mathrm{alg}[B]} \Omega)$ onto the monoid of monoid homomorphisms $\mathrm{WithConv}(H \to_{\mathrm{alg}[B]} \Omega) \to \Omega^{\times}$ such that: (i) for all $g$ and $f$, the value $e(g)(f) \in \Omega^{\times}$, viewed in $\Omega$, is obtained by applying $\mathrm{Algebra.TensorProduct.productMap}$ of $g$ and $\mathrm{id}_\Omega$ to the element of $\mathrm{CartierDual}\,B\,H \otimes_B \Omega$ corresponding, under [`CartierDual.ofDual`](def/HopfAlgebra_CartierDual.html#L956) tensored with the identity of $\Omega$, to the preimage of the $B$-linear map underlying $f$ under the dual-tensor-hom equivalence $\mathrm{Module.Dual}\,B\,H \otimes_B \Omega \cong (H \to_{B} \Omega)$; and (ii) for every $B$-algebra automorphism $\tau$ of $\Omega$ and all $g, f$, one has $e(\tau \circ g)(f) = \tau\big(e(g)(\tau^{-1} \circ f)\big)$.
--
--   This is Cartier duality for a finite flat commutative group scheme read off on $\Omega$-points: under the hypothesis that $H$ has its full complement of $\Omega$-points, the points of the Cartier dual are exactly the $\Omega^\times$-valued characters of the point group, compatibly with the action of the $B$-algebra automorphisms of $\Omega$. It is used by the statements that produce such a Galois-equivariant identification over an algebraically closed field of characteristic zero and over $p$-adic fields, and in turn by the analysis of the inertia action on the points of a finite flat group scheme via cyclotomic characters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FinFlatHopf_dualPoints_equiv_monoidHom.lean

import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option Elab.async false

theorem FinFlatHopf.dualPoints_equiv_monoidHom
    (B : Type) [CommRing B] (H : Type) [CommRing H] [HopfAlgebra B H]
    [Coalgebra.IsCocomm B H] [Module.Finite B H] [Module.Free B H]
    (Ω : Type) [Field Ω] [Algebra B Ω]
    (hcard : Nat.card (WithConv (H →ₐ[B] Ω)) = Module.finrank B H) :
    ∃ e : WithConv (CartierDual B H →ₐ[B] Ω) ≃* (WithConv (H →ₐ[B] Ω) →* Ωˣ),
      (∀ (g : WithConv (CartierDual B H →ₐ[B] Ω)) (f : WithConv (H →ₐ[B] Ω)),
        ((e g f : Ωˣ) : Ω) =
          Algebra.TensorProduct.productMap (WithConv.ofConv g) (AlgHom.id B Ω)
            ((TensorProduct.congr (CartierDual.ofDual B H) (LinearEquiv.refl B Ω))
              ((dualTensorHomEquiv B H Ω).symm (WithConv.ofConv f).toLinearMap))) ∧
      (∀ (τ : Ω ≃ₐ[B] Ω) (g : WithConv (CartierDual B H →ₐ[B] Ω))
          (f : WithConv (H →ₐ[B] Ω)),
        ((e (WithConv.toConv (τ.toAlgHom.comp (WithConv.ofConv g))) f : Ωˣ) : Ω) =
          τ ((e g (WithConv.toConv (τ.symm.toAlgHom.comp (WithConv.ofConv f))) : Ωˣ) : Ω)) := by sorry
