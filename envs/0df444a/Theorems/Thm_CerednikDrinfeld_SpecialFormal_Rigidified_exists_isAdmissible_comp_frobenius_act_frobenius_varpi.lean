-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_comp_frobenius_act_frobenius_varpi
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_comp_frobenius_act_frobenius_varpi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/535e8d9c-0441-52cd-9346-04ad64c34139
-- title:
--   Translate by varpi of an admissible rigidified module exists
-- statement:
--   Let $p$ be a prime and $k$ a perfect field of characteristic $p$, with Witt vectors $W(k)$, and let $\iota\colon \mathbb Z_{p^2}=W(\mathbb F_{p^2})\to W(k)$ be a ring homomorphism. Let $\Phi$ be a formal $\mathcal O_D$-module over $W(k)/pW(k)$ in the sense of the structure `FormalODModule` — a commutative two-dimensional formal group law $F$, an action $a\mapsto[a]$ of $\mathbb Z_{p^2}$ by endomorphisms of $F$ which is additive and multiplicative, and an endomorphism $\varpi$ with $\varpi\circ\varpi=[p]$ and $\varpi\circ[a]=[\mathrm{Fr}(a)]\circ\varpi$ — and assume $\Phi$ has height $4$, i.e. $[p]_\Phi$ has kernel of degree $p^4$. Let $B$ be a commutative ring, $\psi\colon W(k)\to B$ a ring homomorphism, and $t=(X,n,\rho)$ a rigidified object over $B$: a formal $\mathcal O_D$-module $X$ over $B$, an integer $n\ge 0$, and a tuple $\rho$ of power series over $B/pB$. Assume $t$ is admissible for $(\iota,\psi)$: $X$ is special for the structure map built from $\iota$ and $\psi$, $[p]_X$ has kernel of degree $p^4$, and $\rho$ is an isogeny of height $4n$ from `t.Φbar ψ`, the formal $\mathcal O_D$-module over $B/pB$ attached to $\Phi$ and $\psi$, to the reduction $\bar X=X\otimes B/pB$. Then there is a rigidified object $t'=(X',n',\rho')$ over $B$, admissible for $(\iota,\psi\circ\mathrm{Fr})$, such that $X'$ has the same formal group law and the same $\varpi$ as $X$ while $[a]_{X'}=[\mathrm{Fr}(a)]_X$ for all $a\in\mathbb Z_{p^2}$, and such that for some $c\in\mathbb N$ one has the equality of tuples of power series over $B/pB$ $$[p^{c+n}]_{\bar X}\circ\rho'\circ(X_1^p,X_2^p)=[p^{c+n'}]_{\bar X}\circ\rho\circ\varpi_\Phi,$$ where $\varpi_\Phi$ is transported along `residueMap ψ`.
--
--   This is the existence half of the $D^\times$-translation clause in Drinfeld's moduli problem for special formal $\mathcal O_D$-modules: the translate of an admissible rigidified object by the uniformiser $\Pi$ of $\mathcal O_D$ is again admissible, for the Frobenius-twisted structure homomorphism $\psi\circ\mathrm{Fr}$, the identity in the conclusion expressing that $p^{-n'}\rho'$ is the quasi-isogeny $p^{-n}\rho\circ\varpi_\Phi\circ\mathrm{Frob}^{-1}$ (Boutot–Carayol II (9.4)). It is used in the equivariant form of Drinfeld's representability theorem, [`CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_forall_bijective_and_isBaseChange_and_isPullback_omegaObj_of_isZariskiSheaf_of_isNoetherianRing`](thm.html#CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_forall_bijective_and_isBaseChange_and_isPullback_omegaObj_of_isZariskiSheaf_of_isNoetherianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_comp_frobenius_act_frobenius_varpi.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_comp_frobenius_act_frobenius_varpi
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k))) (hΦ4 : Φ.HasHeight 4)
    (B : Type u) [CommRing B] (ψ : WittVector p k →+* B) (t : Rigidified p Φ B)
    (ht : t.IsAdmissible ι ψ) :
    ∃ t' : Rigidified p Φ B,
      t'.IsAdmissible ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) ∧
      t'.X.F = t.X.F ∧ t'.X.varpi = t.X.varpi ∧ (∀ a, t'.X.act a = t.X.act (WittVector.frobenius a)) ∧
      ∃ c : ℕ,
        (t.Xbar.act ((p : Zp2 p) ^ (c + t.n))).comp
            (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal p B)) ^ p) =
          (t.Xbar.act ((p : Zp2 p) ^ (c + t'.n))).comp (t.ρ.comp (Φ.varpi.map (residueMap ψ))) := by sorry
