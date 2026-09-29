-- Prove2me | Theorems.Thm_AddCommGroup_natCard_primaryComponent_ker_aeval_of_forall_natCard_ker_aeval_eq_natAbs_resultant
-- name    : AddCommGroup.natCard_primaryComponent_ker_aeval_of_forall_natCard_ker_aeval_eq_natAbs_resultant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/e91c44d2-d113-5d82-8981-24973b148f5d
-- title:
--   ℓ-primary kernel orders of G(T) from resultants
-- statement:
--   Let $M$ be an additive abelian group and $T\colon M \to M$ an endomorphism of it, let $P \in \mathbb{Z}[X]$ be monic, and let $R$ be a commutative ring which is a domain. Assume the hypothesis $h$: for every monic $G \in \mathbb{Z}[X]$ whose constant coefficient has nonzero image in $R$, the kernel of the $\mathbb{Z}$-linear endomorphism $G(T)$ of $M$ (the evaluation of $G$ at $T$ viewed as a $\mathbb{Z}$-linear map, with kernel taken as an additive subgroup) has cardinality $|\operatorname{Res}(G,P)|$ when $\operatorname{Res}(G,P) \neq 0$, and is infinite when $\operatorname{Res}(G,P) = 0$. Then for every monic $G \in \mathbb{Z}[X]$ — with no condition on its constant coefficient — and every prime $\ell$ whose image in $R$ is nonzero: if $\operatorname{Res}(G,P) \neq 0$, the $\ell$-primary component of $\ker G(T)$, i.e. the subgroup of elements annihilated by a power of $\ell$, has cardinality $\ell^{m}$ where $m$ is the exponent of $\ell$ in the factorisation of the natural number $|\operatorname{Res}(G,P)|$; and if $\operatorname{Res}(G,P) = 0$, that $\ell$-primary component is infinite.
--
--   A purely group-theoretic bootstrap: it removes the restriction on the constant coefficient from a resultant formula for kernel orders, at the cost of passing to $\ell$-primary parts for primes $\ell$ invertible in the coefficient domain $R$. It is used in the study of the group $\mathrm{Pic}^0$ of a curve together with the endomorphism induced by Frobenius, where the orders of kernels of $G(\mathrm{Frob})$ are expressed through resultants with the characteristic polynomial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddCommGroup_natCard_primaryComponent_ker_aeval_of_forall_natCard_ker_aeval_eq_natAbs_resultant.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AddCommGroup.natCard_primaryComponent_ker_aeval_of_forall_natCard_ker_aeval_eq_natAbs_resultant
    {M : Type*} [AddCommGroup M] (T : M →+ M) (P : Polynomial ℤ) (hP : P.Monic)
    (R : Type*) [CommRing R] [IsDomain R]
    (h : ∀ G : Polynomial ℤ, G.Monic → ((G.coeff 0 : ℤ) : R) ≠ 0 →
        (G.resultant P ≠ 0 →
          Nat.card (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom.ker =
            (G.resultant P).natAbs) ∧
        (G.resultant P = 0 →
          ¬ Finite (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom.ker))
    (G : Polynomial ℤ) (hG : G.Monic) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : R) ≠ 0) :
    (G.resultant P ≠ 0 →
      Nat.card (AddCommGroup.primaryComponent
        (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom.ker ℓ) =
        ℓ ^ ((G.resultant P).natAbs.factorization ℓ)) ∧
    (G.resultant P = 0 →
      ¬ Finite (AddCommGroup.primaryComponent
        (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom.ker ℓ)) := by sorry
