-- Prove2me | Theorems.Thm_BurauFaithful_burau_three_spec_twist_pow_six
-- name    : BurauFaithful.burau_three_spec_twist_pow_six
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-29T15:19:47.400795+00:00
-- url     : https://prove2.me/theorems/03788ab5-91a0-4d31-8164-b3333ea7a7ea
-- title:
--   At $t=-1$ the Burau matrix of $\sigma_1\sigma_2$ has order dividing $6$
-- statement:
--   This is a concrete relation satisfied by the Burau representation of the three-strand braid group after evaluating the indeterminate at $t=-1$; it is the "easy half" of the first step of Birman's proof of Theorem 3.15 (J. S. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82, §3.3, pp. 129-130), where the modular group $\mathrm{SL}(2,\mathbb{Z})$ enters.
--
--   Let $B_3 = \langle \sigma_1,\sigma_2 \mid \sigma_1\sigma_2\sigma_1 = \sigma_2\sigma_1\sigma_2\rangle$, let $\rho_3 : B_3 \to \mathrm{GL}_3(\mathbb{Z}[t,t^{-1}])$ be the unreduced Burau representation, and let $\mathbb{Z}[t,t^{-1}]\to\mathbb{Z}$, $t\mapsto-1$ be the specialization. The theorem states that the sixth power of the specialized Burau matrix of $\sigma_1\sigma_2$ is the identity:
--
--   $$\Bigl(\rho_3(\sigma_1\sigma_2)\big|_{t=-1}\Bigr)^6 = I_3 .$$
--
--   Equivalently, the image of the square of the full twist, $\Delta^4 = (\sigma_1\sigma_2)^6$ with $\Delta^2=(\sigma_1\sigma_2)^3$ generating the centre of $B_3$, lies in the kernel of the specialization — which is why the specialization alone cannot detect faithfulness and a second step is needed.
--
--   **Formalization Note** The specialization is written inline as `LaurentPolynomial.eval₂ (Int.castRingHom ℤ) (-1 : ℤˣ)` and extended to matrices by `Matrix.GeneralLinearGroup.map`; the power is a power in the group $\mathrm{GL}_3(\mathbb{Z})$.
-- source:
--   J. S. Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82, Princeton Univ. Press, 1974, Chapter 3 (Magnus representations), §3.3, Theorem 3.15, pp. 129-130 ("setting t = -1 these matrices become ... By [Coxeter-Moser, 1964, p. 85] s1 and s2 generate the homogeneous modular group M2, which has defining relations s1s2s1 = s2s1s2 and (s1s2s1)^4 = 1"); cf. V. Bharathram, J. S. Birman, T. E. Brendle, arXiv:2607.05283v2, Theorem 4.1 (Section 4).

import Definitions.Def_BurauFaithful_UnreducedBurau

set_option autoImplicit false

theorem BurauFaithful.burau_three_spec_twist_pow_six :
    (Matrix.GeneralLinearGroup.map (LaurentPolynomial.eval₂ (Int.castRingHom ℤ) (-1 : ℤˣ))
      (BurauFaithful.burauRep 3 (BraidsLinksMCG.sigma ⟨0, by decide⟩ * BraidsLinksMCG.sigma ⟨1, by decide⟩))) ^ 6 = 1 := by sorry
