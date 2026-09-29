-- Prove2me | Theorems.Thm_CuspForm_exists_alSlash_diamondLinH_eq_diamondLinH_alSlash_atkinLehnerDatum
-- name    : CuspForm.exists_alSlash_diamondLinH_eq_diamondLinH_alSlash_atkinLehnerDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/14f2d882-5dbf-5bda-9044-5e870102f42f
-- title:
--   Atkin–Lehner slash intertwines diamond operators on Γ_H(M)
-- statement:
--   Let $M\neq 0$ and $q$ be natural numbers and let $W$ be an Atkin–Lehner datum for $(M,q)$, that is, a natural number $R$ with $M=qR$ together with integers $a,b$ satisfying $qa-Rb=1$; write $W.\mathrm{alGL}$ for the associated element of $\mathrm{GL}(2,\mathbb{R})$, the real matrix attached to the datum, of determinant $q$. Let $H$ be any subgroup of $(\mathbb{Z}/M)^\times$, let $k$ be an integer, let $d\in(\mathbb{Z}/M)^\times$, and let $f,G$ be weight-$k$ cusp forms for the group $\Gamma_H(M)\le \mathrm{SL}(2,\mathbb{Z})$, the image under the inclusion $\Gamma_0(M)\hookrightarrow \mathrm{SL}(2,\mathbb{Z})$ of the preimage of $H$ under the lower-right-entry homomorphism $\Gamma_0(M)\to(\mathbb{Z}/M)^\times$. Assume that the function underlying $G$ is $f\mid_k W.\mathrm{alGL}$. Then there exists a unit $d'\in(\mathbb{Z}/M)^\times$ such that $d'$ and $d$ have the same image in $(\mathbb{Z}/R)^\times$, the image of $d'd$ in $(\mathbb{Z}/q)^\times$ is $1$, and $(\langle d\rangle f)\mid_k W.\mathrm{alGL}=\langle d'\rangle G$ as functions on the upper half-plane. Here $\langle d\rangle$ denotes [`CuspForm.diamondLinH k d`](def/CuspForm_HeckeOperatorFormsGammaH.html#L132), which is the map $f\mapsto f\mid_k\gamma_d$ for a fixed lift $\gamma_d\in\mathrm{SL}(2,\mathbb{Z})$ of $d$ when the predicate `StableD M H k` holds (vanishing of $f\mid_k\sigma$ at every cusp of $\Gamma_H(M)$, for all $\sigma\in\Gamma_0(M)$ and all such $f$), and is the zero map otherwise.
--
--   This is the commutation rule between an Atkin–Lehner operator $w_q$ and the diamond operators, $w_q\langle d\rangle=\langle d^{*}\rangle w_q$ with $d^{*}\equiv d^{-1}\pmod q$ and $d^{*}\equiv d\pmod{M/q}$, here for an arbitrary Atkin–Lehner datum and an arbitrary subgroup $H$, with the translate $f\mid_k W$ given as a cusp form on $\Gamma_H(M)$. It is used in the study of Hecke operators at the level of two-cusp integral structures and in the comparison of Hecke operators under the twisting correspondence on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_alSlash_diamondLinH_eq_diamondLinH_alSlash_atkinLehnerDatum.lean

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem CuspForm.exists_alSlash_diamondLinH_eq_diamondLinH_alSlash_atkinLehnerDatum
    {M q : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q) (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    (d : (ZMod M)ˣ) (f G : CuspForm (CohCarrier.GammaH M H) k)
    (hG : (⇑G : UpperHalfPlane → ℂ) = ModularForm.alSlash W k ⇑f) :
    ∃ d' : (ZMod M)ˣ,
      ZMod.unitsMap (Dvd.intro_left q W.hM.symm : W.R ∣ M) d' = ZMod.unitsMap (Dvd.intro_left q W.hM.symm : W.R ∣ M) d ∧
      ZMod.unitsMap (Dvd.intro W.R W.hM.symm : q ∣ M) (d' * d) = 1 ∧
      ModularForm.alSlash W k (⇑(CuspForm.diamondLinH k d f) : UpperHalfPlane → ℂ) =
        (⇑(CuspForm.diamondLinH k d' G) : UpperHalfPlane → ℂ) := by sorry
