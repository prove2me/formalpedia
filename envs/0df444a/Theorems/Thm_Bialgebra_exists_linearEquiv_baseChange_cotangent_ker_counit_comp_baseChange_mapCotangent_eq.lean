-- Prove2me | Theorems.Thm_Bialgebra_exists_linearEquiv_baseChange_cotangent_ker_counit_comp_baseChange_mapCotangent_eq
-- name    : Bialgebra.exists_linearEquiv_baseChange_cotangent_ker_counit_comp_baseChange_mapCotangent_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/e7591caf-4df4-5096-855b-668d78ed1959
-- title:
--   Cotangent module at the unit of a bialgebra commutes with base change
-- statement:
--   Let $R$ be a commutative ring, $S$ a commutative $R$-algebra, and $A$ a commutative $R$-bialgebra. Write $I_A = \ker(\varepsilon_A)$ for the kernel of the counit $\varepsilon_A \colon A \to R$, regarded as an $R$-algebra map, and $I_B = \ker(\varepsilon_B)$ for the kernel of the counit of the base-changed $S$-bialgebra $B = S \otimes_R A$; for an ideal $I$, $I$.`Cotangent` denotes $I/I^2$ and `toCotangent` the map sending $x \in I$ to its class. The assertion is that there exists an $S$-linear isomorphism $\Lambda \colon S \otimes_R (I_A/I_A^2) \xrightarrow{\sim} I_B/I_B^2$ such that: (1) for all $s \in S$, $x \in I_A$ and $y \in I_B$ whose underlying element of $S \otimes_R A$ equals $s \otimes x$, one has $\Lambda(s \otimes [x]) = [y]$; and (2) for every $R$-algebra endomorphism $q$ of $A$ together with hypotheses $I_A \le q^{-1}(I_A)$ and $I_B \le (\mathrm{id}_S \otimes q)^{-1}(I_B)$ — the data needed to form the induced maps on cotangent modules — the underlying $S$-linear map of $\Lambda$ composed after the $S$-base change of the map $I_A/I_A^2 \to I_A/I_A^2$ induced by $q$ agrees with the map $I_B/I_B^2 \to I_B/I_B^2$ induced by $\mathrm{id}_S \otimes q$ composed after $\Lambda$.
--
--   In geometric terms this says that the conormal module $\omega_{G/R} = e^*\Omega^1_{G/R} = I_A/I_A^2$ at the unit section of the affine monoid scheme $G = \operatorname{Spec} A$ over $R$ is compatible with arbitrary base change, $\omega_{G_S/S} \cong S \otimes_R \omega_{G/R}$, naturally in endomorphisms of $G$ fixing the unit; no flatness or finiteness hypotheses appear. It is used in the analysis of the cotangent modules of models of modular curves and of the torsion maps acting on them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Bialgebra_exists_linearEquiv_baseChange_cotangent_ker_counit_comp_baseChange_mapCotangent_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

theorem Bialgebra.exists_linearEquiv_baseChange_cotangent_ker_counit_comp_baseChange_mapCotangent_eq
    (R : Type) [CommRing R] (S : Type) [CommRing S] [Algebra R S]
    (A : Type) [CommRing A] [Bialgebra R A] :
    ∃ Λ : S ⊗[R] (RingHom.ker (Bialgebra.counitAlgHom R A)).Cotangent ≃ₗ[S]
        (RingHom.ker (Bialgebra.counitAlgHom S (S ⊗[R] A))).Cotangent,
      (∀ (s : S) (x : ↥(RingHom.ker (Bialgebra.counitAlgHom R A)))
          (y : ↥(RingHom.ker (Bialgebra.counitAlgHom S (S ⊗[R] A)))),
          (y : S ⊗[R] A) = s ⊗ₜ[R] (x : A) →
          Λ (s ⊗ₜ[R] (RingHom.ker (Bialgebra.counitAlgHom R A)).toCotangent x) =
            (RingHom.ker (Bialgebra.counitAlgHom S (S ⊗[R] A))).toCotangent y) ∧
      ∀ (q : A →ₐ[R] A)
        (hq : RingHom.ker (Bialgebra.counitAlgHom R A) ≤
          (RingHom.ker (Bialgebra.counitAlgHom R A)).comap q)
        (hQ : RingHom.ker (Bialgebra.counitAlgHom S (S ⊗[R] A)) ≤
          (RingHom.ker (Bialgebra.counitAlgHom S (S ⊗[R] A))).comap
            (Algebra.TensorProduct.map (AlgHom.id S S) q)),
        (Λ : S ⊗[R] (RingHom.ker (Bialgebra.counitAlgHom R A)).Cotangent →ₗ[S]
            (RingHom.ker (Bialgebra.counitAlgHom S (S ⊗[R] A))).Cotangent) ∘ₗ
          ((RingHom.ker (Bialgebra.counitAlgHom R A)).mapCotangent
              (RingHom.ker (Bialgebra.counitAlgHom R A)) q hq).baseChange S =
        (RingHom.ker (Bialgebra.counitAlgHom S (S ⊗[R] A))).mapCotangent
            (RingHom.ker (Bialgebra.counitAlgHom S (S ⊗[R] A)))
            (Algebra.TensorProduct.map (AlgHom.id S S) q) hQ ∘ₗ
          (Λ : S ⊗[R] (RingHom.ker (Bialgebra.counitAlgHom R A)).Cotangent →ₗ[S]
            (RingHom.ker (Bialgebra.counitAlgHom S (S ⊗[R] A))).Cotangent) := by sorry
