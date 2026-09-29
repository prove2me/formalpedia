-- Prove2me | Theorems.Thm_CohCarrier_jDeg_iDeg_cross_eq_index_smul_heckeT
-- name    : CohCarrier.jDeg_iDeg_cross_eq_index_smul_heckeT
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/259dfa81-cc06-5d20-be62-335196403bb4
-- title:
--   Cross degeneracy composite is an index multiple of T_q
-- statement:
--   Fix natural numbers $M, M', d, d'$, subgroups $H \le (\mathbb{Z}/M)^\times$ and $H' \le (\mathbb{Z}/M')^\times$, an additive commutative group $A$, and a natural number $q$, with $M', d, d', q$ nonzero. Assume two instances of the predicate `LevelLE`: $h$ for the index $d$ and $h'$ for the index $d'$, each asserting $M \mid M'$, that the index divides $M'/M$, and that reduction $(\mathbb{Z}/M')^\times \to (\mathbb{Z}/M)^\times$ carries $H'$ into $H$. Assume further $q \mid d$ in $\mathbb{Z}$ and $d = d'q$. Let $\varphi$ be an element of `H1 M H A`, i.e. an additive homomorphism from `Additive` of $\Gamma_H(M) =$ the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ consisting of the elements of $\Gamma_0(M)$ whose associated unit lies in $H$, to $A$. Then the composite of `iDeg'` at index $d'$ — precomposition with the injection `iotaDeg` at index $d'$, $\gamma \mapsto$ `conjLowerMat d'` $\gamma$, i.e. $\begin{pmatrix} a & b\\ c& e\end{pmatrix} \mapsto \begin{pmatrix} a & bd'\\ c/d' & e\end{pmatrix}$ — with `jDeg` at index $d$ — the additive transfer `coresAdd` from the range of `iotaDeg` at index $d$ up to $\Gamma_H(M)$, applied to the transport of the character along the inverse of the isomorphism onto that range — equals the natural-number multiple of `heckeT M H q A`$\,\varphi$ by the index, inside $\Gamma_H(M) \cap \Gamma_0^{\mathrm{upper}}(q)$ (the elements of $\Gamma_H(M)$ whose upper-right entry vanishes mod $q$), of the subgroup of elements lying in the range of `iotaDeg` at index $d$. Here `heckeT M H q A` is the additive transfer from $\Gamma_H(M) \cap \Gamma_0^{\mathrm{upper}}(q)$ to $\Gamma_H(M)$ of $\varphi$ precomposed with the monomorphism `conjL` at $q$.
--
--   This is the off-diagonal entry of the matrix of the degeneracy pairing at level $(M,H) \le (M',H')$: the composite of the pullback along the degree-$d'$ degeneracy embedding with the corestriction along the degree-$d = d'q$ one is an integral multiple of the Hecke operator $T_q$ (the operator $U_q$ when $q \mid M$). Together with the diagonal identities it is used by the explicit two-, four- and nine-term degeneracy relations [`CohCarrier.jDeg_iDeg_corner_of_prime_sq`](thm.html#CohCarrier.jDeg_iDeg_corner_of_prime_sq), [`CohCarrier.jDeg_iDeg_four_identities_of_dvd`](thm.html#CohCarrier.jDeg_iDeg_four_identities_of_dvd) and [`CohCarrier.jDeg_iDeg_nine_identities_of_prime`](thm.html#CohCarrier.jDeg_iDeg_nine_identities_of_prime), which feed the level-raising and level-lowering comparisons.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_jDeg_iDeg_cross_eq_index_smul_heckeT.lean

import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.jDeg_iDeg_cross_eq_index_smul_heckeT {M M' d d' : ℕ} {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ}
    {A : Type*} [AddCommGroup A] (q : ℕ) [NeZero M'] [NeZero d] [NeZero d'] [NeZero q]
    (h : LevelLE M M' H H' d) (h' : LevelLE M M' H H' d')
    (hqd : (q : ℤ) ∣ (d : ℤ)) (hdiv : d = d' * q) (φ : H1 M H A) :
    (jDeg M M' H H' d A h) ((iDeg' M M' H H' d' A h') φ)
      = (((iotaDeg M M' H H' d h).range).subgroupOf (GammaHUpper M H q)).index
          • heckeT M H q A φ := by sorry
