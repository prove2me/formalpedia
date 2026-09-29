-- Prove2me | Theorems.Thm_CohCarrier_jDeg_comp_coeff
-- name    : CohCarrier.jDeg_comp_coeff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/af1f557e-669d-59e0-afd5-45f5d3e577a8
-- title:
--   Coefficient naturality of the degeneracy trace jDeg
-- statement:
--   Fix a natural number $M$ and a subgroup $H \le (\mathbb{Z}/M)^\times$, abelian groups $A$ and $B$, a natural number $M'$ with $M' \neq 0$, a subgroup $H' \le (\mathbb{Z}/M')^\times$, and a nonzero natural number $d$. Assume `LevelLE M M' H H' d`, that is: $M \mid M'$, $d \mid M'/M$, and the reduction map $(\mathbb{Z}/M')^\times \to (\mathbb{Z}/M)^\times$ carries $H'$ into $H$. Here, for an abelian group $A$, `H1 M H A` denotes $\mathrm{Hom}(\Gamma_H(M), A)$, the additive homomorphisms from the additivisation of $\Gamma_H(M) \le \mathrm{SL}_2(\mathbb{Z})$ — the image under $\Gamma_0(M) \hookrightarrow \mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the determinant-type character `gamma0Units M` — into $A$; and `jDeg M M' H H' d A h` is the map $\mathrm{Hom}(\Gamma_{H'}(M'), A) \to \mathrm{Hom}(\Gamma_H(M), A)$ obtained by transporting a homomorphism along the inverse of the isomorphism of $\Gamma_{H'}(M')$ with the range of the degeneracy embedding `iotaDeg`, and then applying the additive transfer (corestriction) `coresAdd` from that finite-index subgroup of $\Gamma_H(M)$. The assertion is that for every additive homomorphism $g \colon A \to B$ and every $\psi \in \mathrm{Hom}(\Gamma_{H'}(M'), A)$, the degeneracy trace of $g \circ \psi$ equals $g$ composed with the degeneracy trace of $\psi$.
--
--   This records the naturality of the degeneracy trace (transfer, or corestriction) in the coefficient variable, the companion of the analogous statements for the degeneracy pull-back and for the Hecke operators. It is used in the argument that a class whose degeneracy traces vanish, and which is a Hecke eigenvector in the relevant sense, vanishes in the parabolic part at the auxiliary level, where vanishing of traces must be transported along a reduction of coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_jDeg_comp_coeff.lean

import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.jDeg_comp_coeff (M : ℕ) (H : Subgroup (ZMod M)ˣ) {A B : Type}
    [AddCommGroup A] [AddCommGroup B] {M' : ℕ} {H' : Subgroup (ZMod M')ˣ} {d : ℕ}
    [NeZero M'] [NeZero d] (h : LevelLE M M' H H' d) (g : A →+ B) (ψ : H1 M' H' A) :
    jDeg M M' H H' d B h (g.comp ψ) = g.comp (jDeg M M' H H' d A h ψ) := by sorry
