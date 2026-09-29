-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_nonempty_of_isNilpotent_of_isAlgClosed
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.nonempty_of_isNilpotent_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/8e0558b2-33b8-5368-9632-fa0a4d268eda
-- title:
--   Drinfeld data exist over p-nilpotent W(k)-algebras
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, and a commutative ring $B$ which is an algebra over $\mathbb{Z}_p$, together with a ring homomorphism $\psi\colon W(k)\to B$ from the Witt vectors of $k$ and the hypothesis that the image of $p$ in $B$ is nilpotent. The assertion is that the type $\mathrm{DrinfeldDatum}$ formed with $\mathcal{O}=\mathbb{Z}_p$, $K=\mathbb{Q}_p$, uniformiser $\pi=p$ and base ring $B$ is nonempty, i.e. there exists such a datum. A datum of this kind consists of: two families $N_0,N_1\colon \operatorname{Spec} B\to$ (submodules of $\mathbb{Q}_p^2$ over $\mathbb{Z}_p$), each value being a full lattice in the sense of being finitely generated and spanning $\mathbb{Q}_p^{2}$ over $\mathbb{Q}_p$, with $N_0(x)\subseteq N_1(x)$ and $p\,N_1(x)\subseteq N_0(x)$ for every $x$, and with $\{x : v\in N_i(x)\}$ open in $\operatorname{Spec} B$ for each $v\in\mathbb{Q}_p^2$ and $i=0,1$; two $B$-modules $T_0,T_1$ that are invertible over $B$, with $B$-linear maps $\Pi_0\colon T_0\to T_1$ and $\Pi_1\colon T_1\to T_0$ whose two composites are both multiplication by $p$; and, for each $x\in\operatorname{Spec} B$, $B_x$-linear maps $u_i(x)\colon B_x\otimes_{\mathbb{Z}_p} N_i(x)\to (T_i)_x$ into the localisations at the prime complement of $x$, required to be compatible with the inclusion $N_0(x)\subseteq N_1(x)$ and $\Pi_0$, with multiplication by $p$ from $N_1(x)$ to $N_0(x)$, and with the further conditions imposed by the structure (summarised here).
--
--   This is the nonemptiness of Drinfeld's functor of $p$-divisible data, in the stalkwise lattice formulation, on the category of $W(k)$-algebras in which $p$ is nilpotent (Drinfeld 1976, §2; Boutot–Carayol I, Déf. 5.1). It is used in the Čerednik–Drinfeld comparison statement [`CerednikDrinfeld.SpecialFormal.Rigidified.exists_drinfeldDatum_isIsomorphic_iff_and_exists_cover_and_isBaseChange_of_isAdmissible`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.exists_drinfeldDatum_isIsomorphic_iff_and_exists_cover_and_isBaseChange_of_isAdmissible), where a datum must be produced over an arbitrary test algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_nonempty_of_isNilpotent_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.nonempty_of_isNilpotent_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (B : Type) [CommRing B] [Algebra ℤ_[p] B]
    (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)) :
    Nonempty (DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) := by sorry
