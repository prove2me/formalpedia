-- Prove2me | Theorems.Thm_Deformation_DieudonneModule_exists_ker_verschiebung_addEquiv_primitives_apply_of_eq_and_apply_map
-- name    : Deformation.DieudonneModule.exists_ker_verschiebung_addEquiv_primitives_apply_of_eq_and_apply_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/11bdffda-5785-5780-ad22-7185901b3a04
-- title:
--   Kernel of Verschiebung equals the primitives, equivariantly
-- statement:
--   Let $k$ be a field of characteristic $p$ for a prime $p$, and let $A$ be a commutative ring carrying a Hopf algebra structure over $k$. For each $n$, $\mathrm{wittHom}\,k\,p\,n\,A$ denotes the additive subgroup of $\mathrm{TruncatedWittVector}\,p\,n\,A$ of those $x$ whose image under the coefficientwise map induced by the comultiplication $A \to A \otimes_k A$ equals the sum of its images under the coefficientwise maps induced by the two inclusions $A \to A \otimes_k A$; $\mathrm{DieudonneModule}\,k\,p\,A$ is the direct limit of these groups along the shift maps, with $\mathrm{of}\,k\,p\,A\,n$ the canonical map from level $n$, $\mathrm{verschiebung}$ the additive endomorphism induced by the truncated Witt vector Verschiebung, and $\mathrm{map}\,k\,p\,\psi$ the additive endomorphism induced coefficientwise by a bialgebra map $\psi$. Finally $\mathrm{primitives}\,k\,A$ is the $k$-submodule of $x \in A$ with $\Delta x - x \otimes 1 - 1 \otimes x = 0$. The assertion is that there exists an additive group isomorphism $e$ from the kernel of $\mathrm{verschiebung}$ onto $\mathrm{primitives}\,k\,A$ such that: for every $x \in \mathrm{wittHom}\,k\,p\,1\,A$ whose image under $\mathrm{of}\,k\,p\,A\,1$ lies in that kernel, $e$ of this image is the $0$th coefficient of $x$; and for every bialgebra endomorphism $\psi$ of $A$ over $k$ and every $z$ in the kernel with $\mathrm{map}\,k\,p\,\psi\,z$ again in the kernel, $e$ of the latter equals $\psi$ applied to $e(z)$.
--
--   This is Oda's identification of the Verschiebung-kernel of the Dieudonné module of a commutative affine group scheme with $\operatorname{Hom}(G,\mathbb{G}_a)$, i.e. with the primitive elements of its coordinate Hopf algebra, in the form pinned down on level one and equivariant for bialgebra endomorphisms. The level-one normalisation together with the equivariance is what lets the isomorphism transport families of operators, and it is used in the counting of the quotient of the Dieudonné module by the Verschiebung image together with the images of such operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_DieudonneModule_exists_ker_verschiebung_addEquiv_primitives_apply_of_eq_and_apply_map.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Deformation.DieudonneModule.exists_ker_verschiebung_addEquiv_primitives_apply_of_eq_and_apply_map
    (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type*) [CommRing A] [HopfAlgebra k A] :
    ∃ e : (Deformation.DieudonneModule.verschiebung k p A).ker ≃+ ↥(primitives k A),
      (∀ (x : Deformation.wittHom k p 1 A)
          (hx : Deformation.DieudonneModule.of k p A 1 x ∈ (Deformation.DieudonneModule.verschiebung k p A).ker),
        (e ⟨Deformation.DieudonneModule.of k p A 1 x, hx⟩ : A) = (x : TruncatedWittVector p 1 A).coeff 0) ∧
      ∀ (ψ : A →ₐc[k] A) (z : (Deformation.DieudonneModule.verschiebung k p A).ker)
        (hz : Deformation.DieudonneModule.map k p ψ z ∈ (Deformation.DieudonneModule.verschiebung k p A).ker),
        (e ⟨Deformation.DieudonneModule.map k p ψ z, hz⟩ : A) = ψ (e z : A) := by sorry
