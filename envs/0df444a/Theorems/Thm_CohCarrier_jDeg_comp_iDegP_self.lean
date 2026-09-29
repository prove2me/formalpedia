-- Prove2me | Theorems.Thm_CohCarrier_jDeg_comp_iDegP_self
-- name    : CohCarrier.jDeg_comp_iDegP_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/6826cecc-424d-5da9-865d-e0c032a5641d
-- title:
--   Corestriction after degeneracy pullback is multiplication by the index
-- statement:
--   Fix naturals $M, M', d$, a subgroup $H \le (\mathbb{Z}/M)^\times$, a subgroup $H' \le (\mathbb{Z}/M')^\times$ and an additive commutative group $A$, with $M'$ and $d$ nonzero. Let $h$ be a `LevelLE` witness, i.e. $M \mid M'$, $d \mid M'/M$, and reduction modulo $M$ carries $H'$ into $H$. Write $\Gamma_H(M)$ for `GammaH M H`, the image in $SL(2,\mathbb{Z})$ of the preimage of $H$ under the lower-right-unit character on $\Gamma_0(M)$, and let $H^1(M,H;A)$ denote the additive homomorphisms $\mathrm{Additive}\,\Gamma_H(M) \to A$. Let $\iota_d =$ `iotaDeg` be the degeneracy embedding $\Gamma_{H'}(M') \to \Gamma_H(M)$ sending $\begin{pmatrix} a & b \\ c & e\end{pmatrix}$ to $\begin{pmatrix} a & bd \\ c/d & e\end{pmatrix}$. Then for every $\varphi \in H^1(M,H;A)$, applying `iDeg'` (precomposition with $\iota_d$) and then `jDeg` (the transfer-based corestriction of the character obtained by transporting $\varphi$ along the inverse of the isomorphism of $\Gamma_{H'}(M')$ onto the range of $\iota_d$) returns $n \cdot \varphi$, where $n$ is the index of the range of $\iota_d$ in $\Gamma_H(M)$.
--
--   This is the standard relation $\mathrm{cores} \circ \mathrm{res} = [\,\Gamma : \Gamma'\,]$ for the degeneracy maps between group cohomology in degree one at levels $M$ and $M'$, in the concrete form of additive characters of the relevant congruence subgroups. It is the diagonal entry in the matrices of identities between degeneracy and corestriction operators, and is cited by the computations of the four- and five-term identities for prime and prime-square level raising, such as [`CohCarrier.jDeg_iDeg_four_identities_of_dvd`](thm.html#CohCarrier.jDeg_iDeg_four_identities_of_dvd) and [`CohCarrier.exists_atkinLehnerOp_iDegL_jDegL_five_identities_of_prime`](thm.html#CohCarrier.exists_atkinLehnerOp_iDegL_jDegL_five_identities_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_jDeg_comp_iDegP_self.lean

import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.jDeg_comp_iDegP_self {M M' d : ℕ} {H : Subgroup (ZMod M)ˣ}
    {H' : Subgroup (ZMod M')ˣ} {A : Type*} [AddCommGroup A] [NeZero M'] [NeZero d]
    (h : LevelLE M M' H H' d) (φ : H1 M H A) :
    jDeg M M' H H' d A h (iDeg' M M' H H' d A h φ)
      = (iotaDeg M M' H H' d h).range.index • φ := by sorry
