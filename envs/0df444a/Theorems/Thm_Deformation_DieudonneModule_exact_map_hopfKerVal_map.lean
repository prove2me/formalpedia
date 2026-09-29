-- Prove2me | Theorems.Thm_Deformation_DieudonneModule_exact_map_hopfKerVal_map
-- name    : Deformation.DieudonneModule.exact_map_hopfKerVal_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/7f958e85-34a9-5f55-8bf8-30f7b0257767
-- title:
--   Left exactness of the Dieudonné module functor
-- statement:
--   Let $k$ be a field and $p$ a prime. Let $A$ be a commutative ring which is a Hopf algebra over $k$ whose comultiplication is cocommutative, let $B$ be a commutative ring which is a Hopf algebra over $k$, and let $\pi \colon A \to B$ be a $k$-bialgebra homomorphism. Write $C = \mathrm{hopfKer}\,\pi$ for the $k$-subalgebra of $A$ on which the coaction $(\mathrm{id}\otimes\pi)\circ\Delta \colon A \to A\otimes_k B$ agrees with $a \mapsto a\otimes 1$, and $\mathrm{hopfKerVal}\,\pi \colon C \to A$ for the inclusion, regarded as a $k$-bialgebra homomorphism. For a commutative $k$-bialgebra $D$, $\mathrm{DieudonneModule}\;k\;p\;D$ is the direct limit, along the maps induced by the shift $\mathrm{TruncatedWittVector}\,p\,n \to \mathrm{TruncatedWittVector}\,p\,(n+1)$, of the additive subgroups $\mathrm{wittHom}\;k\;p\;n\;D \subseteq \mathrm{TruncatedWittVector}\,p\,n\,D$ of those $x$ with $W_n(\Delta)(x) = W_n(\mathrm{incl}_1)(x) + W_n(\mathrm{incl}_2)(x)$ in $\mathrm{TruncatedWittVector}\,p\,n\,(D\otimes_k D)$, and a bialgebra map induces the additive map obtained by applying it to Witt coordinates. The assertion is that the pair of induced additive maps $\mathrm{DieudonneModule}\;k\;p\;C \to \mathrm{DieudonneModule}\;k\;p\;A \to \mathrm{DieudonneModule}\;k\;p\;B$ is exact, i.e. an element of the middle group is annihilated by the second map exactly when it lies in the image of the first.
--
--   In geometric terms, with $G = \operatorname{Spec} A$ and $H = \operatorname{Spec} B$, this is the left exactness of the contravariant Dieudonné module functor $D \mapsto \varinjlim_n \operatorname{Hom}(\operatorname{Spec} D, W_n)$: the homomorphisms $G \to W_n$ killed by restriction along $H \to G$ are those factoring through the Hopf kernel. It is used in the computation of Dieudonné modules of finite flat group schemes over a local ring, in particular in the results on ranks and cardinalities obtained from Cartier duality and in the construction of surjections with prescribed kernel.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_DieudonneModule_exact_map_hopfKerVal_map.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem Deformation.DieudonneModule.exact_map_hopfKerVal_map
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime]
    {A : Type v} [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A]
    {B : Type w} [CommRing B] [HopfAlgebra k B]
    (π : A →ₐc[k] B) :
    Function.Exact (Deformation.DieudonneModule.map k p (HopfAlgebra.hopfKerVal π))
      (Deformation.DieudonneModule.map k p π) := by sorry
