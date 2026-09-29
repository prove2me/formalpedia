-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_endAct_actEnd_eq_map_smul_of_frobenius_eq_of_isNilpotent
-- name    : CerednikDrinfeld.FormalODModule.endAct_actEnd_eq_map_smul_of_frobenius_eq_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/872e2705-b8c5-5ca9-8293-6d6384e7a442
-- title:
--   Frobenius-fixed scalars act through W(j)∘θ on Cartier modules
-- statement:
--   Fix a prime $p$ and a commutative ring $B$, write $\mathbb{Z}_{p^2}$ for $W(\mathbb{F}_{p^2})$ (the Witt vectors of the field `GaloisField p 2`), and let $j\colon\mathbb{Z}_{p^2}\to B$ be a ring homomorphism with $p$ nilpotent in $B$. Let $X$ be a formal $\mathcal{O}_D$-module over $B$, that is: a commutative two-dimensional formal group law $X.F$ over $B$, a family $a\mapsto X.\mathrm{act}\,a$ of pairs of power series in two variables, each a law endomorphism of $X.F$, together with a law endomorphism $X.\mathrm{varpi}$, such that $\mathrm{act}\,1$ is the identity, $\mathrm{act}(ab)$ is the substitution composite of $\mathrm{act}\,a$ and $\mathrm{act}\,b$, $\mathrm{act}(a+b)$ is the sum of $\mathrm{act}\,a$ and $\mathrm{act}\,b$ formed via $X.F$, $\mathrm{varpi}\circ\mathrm{varpi}=\mathrm{act}\,p$, and $\mathrm{varpi}\circ\mathrm{act}\,a=\mathrm{act}(\sigma a)\circ\mathrm{varpi}$ for $\sigma$ the Witt-vector Frobenius. Let $\theta\colon\mathbb{Z}_{p^2}\to W(\mathbb{Z}_{p^2})$ be a ring homomorphism whose ghost components satisfy $\mathrm{gh}_n(\theta a)=\sigma^n(a)$ for all $a$ and all $n$, and let $a\in\mathbb{Z}_{p^2}$ satisfy $\sigma a=a$. Then for every element $f$ of the Cartier module of $X.F$ — a $2$-tuple of power series in variables indexed by $\mathbb{N}$, with zero constant terms, satisfying the functional equation relating substitution of the Witt addition family to the $X.F$-sum of the two coordinate substitutions — the pushforward of $f$ along the endomorphism $X.\mathrm{actEnd}\,a$ of $X.F$ determined by $\mathrm{act}\,a$ equals the scalar multiple of $f$ by the Witt vector $W(j)(\theta a)\in W(B)$.
--
--   This identifies the action of the Frobenius-fixed part $\mathbb{Z}_p\subset\mathbb{Z}_{p^2}$ on the Cartier module of a formal $\mathcal{O}_D$-module over a $p$-nilpotent base with multiplication by Witt scalars obtained from the Cartier–Dwork section $\theta$. It is used in the analysis of the $\mathbb{Z}_{p^2}$-eigenspace decomposition of the Cartier module, namely in [`CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent`](thm.html#CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent), within the Čerednik–Drinfeld uniformisation framework.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_endAct_actEnd_eq_map_smul_of_frobenius_eq_of_isNilpotent.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.endAct_actEnd_eq_map_smul_of_frobenius_eq_of_isNilpotent
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (hB : IsNilpotent (p : B)) (X : CerednikDrinfeld.FormalODModule p B)
    (θ : CerednikDrinfeld.Zp2 p →+* WittVector p (CerednikDrinfeld.Zp2 p))
    (hθ : ∀ (a : CerednikDrinfeld.Zp2 p) (n : ℕ),
      WittVector.ghostComponent n (θ a) = (⇑(WittVector.frobenius (p := p) (R := GaloisField p 2)))^[n] a)
    (a : CerednikDrinfeld.Zp2 p) (ha : WittVector.frobenius a = a)
    (f : MvFormalGroup.CartierModule p X.F) :
    MvFormalGroup.CartierModule.endAct (X.actEnd a) f = WittVector.map j (θ a) • f := by sorry
