-- Prove2me | Theorems.Thm_Deformation_DieudonneModule_exists_bijective_map_eq_of_addEquiv_of_isLocalRing_cartierDual
-- name    : Deformation.DieudonneModule.exists_bijective_map_eq_of_addEquiv_of_isLocalRing_cartierDual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/cea1b289-390b-591c-a420-12db870aeb96
-- title:
--   Dieudonné isomorphisms over Fₚ come from bialgebra isomorphisms
-- statement:
--   Let $p$ be a prime and let $A$ and $B$ be commutative rings carrying Hopf algebra structures over $\mathbf{Z}/p$ whose comultiplications are cocommutative and which are finite as $\mathbf{Z}/p$-modules. Assume that the Cartier duals $\mathrm{CartierDual}\,(\mathbf{Z}/p)\,A$ and $\mathrm{CartierDual}\,(\mathbf{Z}/p)\,B$ — the linear duals $\mathrm{Hom}_{\mathbf{Z}/p}(A,\mathbf{Z}/p)$, $\mathrm{Hom}_{\mathbf{Z}/p}(B,\mathbf{Z}/p)$ with their convolution ring structures — are local rings. Here $\mathrm{DieudonneModule}\,(\mathbf{Z}/p)\,p\,A$ is the direct limit, along the shift maps, of the additive subgroups $\mathrm{wittHom}$ of $\mathrm{TruncatedWittVector}\,p\,n\,A$ consisting of those truncated Witt vectors $x$ with $\Delta_*x = (\iota_1)_*x + (\iota_2)_*x$, where $\Delta$ is the comultiplication of $A$ and $\iota_1,\iota_2 \colon A \to A \otimes_{\mathbf{Z}/p} A$ are the two inclusions, and it carries the additive endomorphisms `frobenius` and `verschiebung` induced levelwise by the Frobenius and Verschiebung of truncated Witt vectors. Let $e$ be an isomorphism of additive groups from $\mathrm{DieudonneModule}\,(\mathbf{Z}/p)\,p\,B$ to $\mathrm{DieudonneModule}\,(\mathbf{Z}/p)\,p\,A$ commuting with `frobenius` and with `verschiebung`. Then there exists a bialgebra homomorphism $g \colon B \to A$ over $\mathbf{Z}/p$ which is bijective and whose induced additive map $\mathrm{DieudonneModule}\,(\mathbf{Z}/p)\,p\,B \to \mathrm{DieudonneModule}\,(\mathbf{Z}/p)\,p\,A$, given by pushing forward truncated Witt vectors along $g$, equals the underlying additive homomorphism of $e$.
--
--   This is the isomorphism case of the full faithfulness of the Dieudonné functor on finite commutative unipotent group schemes over $\mathbf{F}_p$, the locality of the Cartier dual expressing unipotence of the dual group scheme. It is used in the construction of $p$-divisible towers attached to Dieudonné data, towards the integral $p$-adic study of the Galois deformation problem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_DieudonneModule_exists_bijective_map_eq_of_addEquiv_of_isLocalRing_cartierDual.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem Deformation.DieudonneModule.exists_bijective_map_eq_of_addEquiv_of_isLocalRing_cartierDual
    (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [HopfAlgebra (ZMod p) A] [Coalgebra.IsCocomm (ZMod p) A]
    [Module.Finite (ZMod p) A]
    (B : Type v) [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B]
    [Module.Finite (ZMod p) B]
    (hA : IsLocalRing (CartierDual (ZMod p) A)) (hB : IsLocalRing (CartierDual (ZMod p) B))
    (e : Deformation.DieudonneModule (ZMod p) p B ≃+ Deformation.DieudonneModule (ZMod p) p A)
    (heF : ∀ z, e (Deformation.DieudonneModule.frobenius (ZMod p) p B z) =
      Deformation.DieudonneModule.frobenius (ZMod p) p A (e z))
    (heV : ∀ z, e (Deformation.DieudonneModule.verschiebung (ZMod p) p B z) =
      Deformation.DieudonneModule.verschiebung (ZMod p) p A (e z)) :
    ∃ g : B →ₐc[ZMod p] A, Function.Bijective g ∧
      Deformation.DieudonneModule.map (ZMod p) p g = e.toAddMonoidHom := by sorry
