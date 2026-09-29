-- Prove2me | Theorems.Thm_Deformation_DieudonneModule_natCard_ker_frobenius_eq_natCard_quot_range_verschiebung_of_nonempty_bialgEquiv_cartierDual_zmodp
-- name    : Deformation.DieudonneModule.natCard_ker_frobenius_eq_natCard_quot_range_verschiebung_of_nonempty_bialgEquiv_cartierDual_zmodp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/be15a5b5-bb8a-5c9d-90d6-bda6d71843b1
-- title:
--   Self-dual local–local Dieudonné modules: #ker F=#cokerV
-- statement:
--   Fix a prime $p$ and a commutative ring $A$ carrying a Hopf algebra structure over $\mathbb{Z}/p$ whose comultiplication is cocommutative and which is finite as a $\mathbb{Z}/p$-module. Assume three further hypotheses: $A$ is a local ring; the Cartier dual $\mathrm{CartierDual}\,(\mathbb{Z}/p)\,A$, namely the $\mathbb{Z}/p$-linear dual $\mathrm{Hom}_{\mathbb{Z}/p}(A,\mathbb{Z}/p)$ with its induced bialgebra structure, is also a local ring; and the type of $\mathbb{Z}/p$-bialgebra equivalences $A \simeq \mathrm{CartierDual}\,(\mathbb{Z}/p)\,A$ is nonempty, i.e. $A$ is isomorphic to its Cartier dual as a bialgebra. Let $M = \mathrm{DieudonneModule}\,(\mathbb{Z}/p)\,p\,A$ be the direct limit, along the shift maps, of the additive subgroups $\mathrm{wittHom}\,(\mathbb{Z}/p)\,p\,n\,A$ of $\mathbb{Z}/p$-truncated Witt vectors $x$ of length $n$ with entries in $A$ satisfying the primitivity condition that $x$ pushed forward along the comultiplication equals the sum of its pushforwards along the two inclusions $A \to A \otimes_{\mathbb{Z}/p} A$; it carries the endomorphisms $\mathrm{frobenius}$ and $\mathrm{verschiebung}$ induced levelwise by the Frobenius and Verschiebung of truncated Witt vectors. The conclusion is the equality of natural-number cardinalities $\#\ker(F) = \#\bigl(M/\operatorname{im}(V)\bigr)$.
--
--   This is the numerical shadow, for a finite commutative group scheme over the prime field that is local–local and isomorphic to its Cartier dual, of the Cartier–Dieudonné duality $M(G^{D}) \cong M(G)^{\vee}$ interchanging $F$ and $V$: only the equality of orders of $\ker F$ and $\operatorname{coker} V$ is asserted, no pairing. It is used by [`Deformation.DieudonneModule.natCard_ker_frobenius_eq_natCard_quot_range_verschiebung_of_cyclotomicPairing`](thm.html#Deformation.DieudonneModule.natCard_ker_frobenius_eq_natCard_quot_range_verschiebung_of_cyclotomicPairing), in the line of argument following Mazur's multiplicity-one analysis of self-dual group schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_DieudonneModule_natCard_ker_frobenius_eq_natCard_quot_range_verschiebung_of_nonempty_bialgEquiv_cartierDual_zmodp.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_Dieudonne_WittHomColimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe v

theorem Deformation.DieudonneModule.natCard_ker_frobenius_eq_natCard_quot_range_verschiebung_of_nonempty_bialgEquiv_cartierDual_zmodp
    (p : ℕ) [Fact p.Prime]
    (A : Type v) [CommRing A] [HopfAlgebra (ZMod p) A] [Coalgebra.IsCocomm (ZMod p) A]
    [Module.Finite (ZMod p) A]
    (hloc : IsLocalRing A) (hdual : IsLocalRing (CartierDual (ZMod p) A))
    (hself : Nonempty (A ≃ₐc[ZMod p] CartierDual (ZMod p) A)) :
    Nat.card (Deformation.DieudonneModule.frobenius (ZMod p) p A).ker =
      Nat.card (Deformation.DieudonneModule (ZMod p) p A ⧸
        (Deformation.DieudonneModule.verschiebung (ZMod p) p A).range) := by sorry
