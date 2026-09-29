-- Prove2me | Theorems.Thm_Algebra_FormallyEtale_exists_baseChange_algEquiv_of_isReduced_zmodp
-- name    : Algebra.FormallyEtale.exists_baseChange_algEquiv_of_isReduced_zmodp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/8696d60d-d50b-574f-ab57-8eb9642304df
-- title:
--   Reduced finite 𝔽ₚ-algebras lift to formally étale 𝒪-algebras
-- statement:
--   Let $\mathcal{O}$ be a commutative ring and $p$ a prime number. Assume: the image of $p$ in $\mathcal{O}$ is a non-zero-divisor; $\mathcal{O}$ carries an algebra structure over $\mathbb{Z}/p$, i.e. a ring homomorphism $\mathcal{O} \to \mathbb{Z}/p$ (necessarily surjective), whose kernel is the principal ideal $(p)$, so that $\mathcal{O}/p\mathcal{O} \cong \mathbb{Z}/p$; and $\mathcal{O}$ is complete and Hausdorff for the $(p)$-adic filtration. Let $\bar H$ be a commutative ring equipped with a $\mathbb{Z}/p$-algebra structure, finite as a $\mathbb{Z}/p$-module, and reduced. Then there exist a type $H$ (in the same universe as $\mathcal{O}$), a commutative ring structure on $H$, an $\mathcal{O}$-algebra structure on $H$ making $H$ free and finite as an $\mathcal{O}$-module, and a proof that $H$ is formally étale over $\mathcal{O}$, such that the $\mathcal{O}$-rank of $H$ equals $\dim_{\mathbb{Z}/p} \bar H$ and the base change $\mathbb{Z}/p \otimes_{\mathcal{O}} H$, formed along the given map $\mathcal{O} \to \mathbb{Z}/p$, is isomorphic to $\bar H$ as a $\mathbb{Z}/p$-algebra (the type of such isomorphisms is asserted to be nonempty).
--
--   This is the essentially surjective half of the equivalence between finite étale algebras over a $p$-adically complete ring with residue ring $\mathbb{F}_p$ and finite étale algebras over $\mathbb{F}_p$, in the concrete shape needed here: a reduced finite $\mathbb{F}_p$-algebra is a product of finite fields and lifts to a product of unramified extensions of $\mathcal{O}$. It is used by [`HopfAlgebra.exists_formallyEtale_bialgEquiv_baseChange_zmodp`](thm.html#HopfAlgebra.exists_formallyEtale_bialgEquiv_baseChange_zmodp) to produce the formally étale part of a finite Hopf algebra over $\mathcal{O}$ with prescribed reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_FormallyEtale_exists_baseChange_algEquiv_of_isReduced_zmodp.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

universe u v

theorem Algebra.FormallyEtale.exists_baseChange_algEquiv_of_isReduced_zmodp
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (Hbar : Type v) [CommRing Hbar] [Algebra (ZMod p) Hbar] [Module.Finite (ZMod p) Hbar] [IsReduced Hbar] :
    ∃ (H : Type u) (_ : CommRing H) (_ : Algebra 𝓞 H) (_ : Module.Free 𝓞 H) (_ : Module.Finite 𝓞 H)
      (_ : Algebra.FormallyEtale 𝓞 H),
      Module.finrank 𝓞 H = Module.finrank (ZMod p) Hbar ∧
      Nonempty ((ZMod p ⊗[𝓞] H) ≃ₐ[ZMod p] Hbar) := by sorry
