-- Prove2me | Theorems.Thm_BurauFaithful_burau_three_spec_coxeter
-- name    : BurauFaithful.burau_three_spec_coxeter
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-29T15:20:06.830224+00:00
-- url     : https://prove2.me/theorems/5bde7ddb-7d0b-417a-a611-bafbd520a137
-- title:
--   The Coxeter relation $(\rho_3(\sigma_1\sigma_2\sigma_1)|_{t=-1})^4 = 1$
-- statement:
--   This is the Coxeter relation of the homogeneous modular group, realized by the Burau matrices specialized at $t=-1$. It is the extra relation, beyond the braid relation, that identifies the image of the specialization with $\mathrm{SL}(2,\mathbb{Z})$ in Birman's proof of Theorem 3.15 (J. S. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82, §3.3, pp. 129-130, citing Moser-Coxeter 1964, p. 85).
--
--   Let $B_3 = \langle \sigma_1,\sigma_2 \mid \sigma_1\sigma_2\sigma_1=\sigma_2\sigma_1\sigma_2\rangle$, let $\rho_3$ be the unreduced Burau representation and let $t\mapsto-1$ be the specialization. With $\Delta=\sigma_1\sigma_2\sigma_1$ the Garside element, the theorem states
--
--   $$\Bigl(\rho_3(\Delta)\big|_{t=-1}\Bigr)^4 = I_3 ,$$
--
--   i.e. the fourth power of the specialized Burau matrix of $\sigma_1\sigma_2\sigma_1$ is the identity. Together with the braid relation, which the specialized matrices satisfy because they satisfy it over $\mathbb{Z}[t,t^{-1}]$, this exhibits the specialized matrices as generators of the homogeneous modular group $M_2=\mathrm{SL}(2,\mathbb{Z})$, whose defining relations are $s_1s_2s_1=s_2s_1s_2$ and $(s_1s_2s_1)^4=1$.
--
--   **Formalization Note** The specialization is `LaurentPolynomial.eval₂ (Int.castRingHom ℤ) (-1 : ℤˣ)`, extended to matrices by `Matrix.GeneralLinearGroup.map`.
-- source:
--   J. S. Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82, Princeton Univ. Press, 1974, Chapter 3 (Magnus representations), §3.3, Theorem 3.15, pp. 129-130 ("setting t = -1 these matrices become ... By [Coxeter-Moser, 1964, p. 85] s1 and s2 generate the homogeneous modular group M2, which has defining relations s1s2s1 = s2s1s2 and (s1s2s1)^4 = 1"); cf. V. Bharathram, J. S. Birman, T. E. Brendle, arXiv:2607.05283v2, Theorem 4.1 (Section 4).

import Definitions.Def_BurauFaithful_UnreducedBurau

set_option autoImplicit false

theorem BurauFaithful.burau_three_spec_coxeter :
    (Matrix.GeneralLinearGroup.map (LaurentPolynomial.eval₂ (Int.castRingHom ℤ) (-1 : ℤˣ))
      (BurauFaithful.burauRep 3 (BraidsLinksMCG.sigma ⟨0, by decide⟩ * BraidsLinksMCG.sigma ⟨1, by decide⟩ * BraidsLinksMCG.sigma ⟨0, by decide⟩))) ^ 4 = 1 := by sorry
