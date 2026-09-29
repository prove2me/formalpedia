-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_digit_eq_mul_pow_add_mul_of_varpi_eq_verschiebung
-- name    : CerednikDrinfeld.GradedCartierModuleData.exists_digit_eq_mul_pow_add_mul_of_varpi_eq_verschiebung
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/9f8311e4-3bf6-56a0-90de-b6c19a3dd191
-- title:
--   Artin–Schreier relation for the leading digit at a critical index
-- statement:
--   Fix a prime $p$, a commutative ring $B$, and a ring homomorphism $j$ from $W(\mathbb{F}_{p^2})$ to $B$, and let $D$ be a graded Cartier module datum for these data: a $W(B)$-module $M$ equipped with additive maps $F$ (`frobenius`) and $V$ (`verschiebung`), a $W(B)$-linear map $\Pi$ (`varpi`), and submodules $M_0,M_1$ indexed by $\mathrm{Fin}\,2$, subject to the axioms $F(w\cdot x)=\sigma(w)\cdot F x$, $w\cdot Vx=V(\sigma(w)\cdot x)$, $V(w\cdot Fx)=V(w)\cdot x$, $F(Vx)=px$, $\Pi V=V\Pi$, $\Pi F=F\Pi$, $\Pi^2=p$, complementarity of $M_0$ and $M_1$, and $V,F,\Pi$ each carrying $M_i$ into $M_{i+1}$. Let $\gamma:\mathrm{Fin}\,2\to M$ be a homogeneous $V$-basis, i.e. $\gamma_i\in M_i$ and every $x\in M$ is written uniquely as $x=\sum_i [c_i]\gamma_i+Vy$ with $c\in B^{\mathrm{Fin}\,2}$, $y\in M$, where $[\,\cdot\,]$ denotes the Teichmüller lift. Let $i\in\mathrm{Fin}\,2$, let $x_i,x_{\mathrm{next}}\in M$ and $a\in B$ satisfy $\Pi\gamma_i=Vx_i$ and $\Pi\gamma_{i+1}=[a]\gamma_i+Vx_{\mathrm{next}}$, and let $m\in M_i$ satisfy $\Pi m=Vm$. Then there exist $c,d,b\in B$ and $m_2,x'\in M$ with $m=[c]\gamma_i+V([d]\gamma_{i+1}+Vm_2)$, $x_i=[b]\gamma_i+Vx'$, and the exact identity $c=bc^p+ad$.
--
--   This is the Artin–Schreier-type relation satisfied by the leading digit of a $\Pi=V$ invariant element at a critical index, in the Cartier-module description of special formal $\mathcal{O}_D$-modules used in the Čerednik–Drinfeld uniformisation (Boutot–Carayol, II (6.5)–(6.7)); the relation is exact, with no error term. It is used in the descent step [`CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_nsmul_eq_lambda_of_varpi_eq_teichmuller_smul_add_verschiebung`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_nsmul_eq_lambda_of_varpi_eq_teichmuller_smul_add_verschiebung).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_exists_digit_eq_mul_pow_add_mul_of_varpi_eq_verschiebung.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.GradedCartierModuleData.exists_digit_eq_mul_pow_add_mul_of_varpi_eq_verschiebung
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : Zp2 p →+* B)
    (D : GradedCartierModuleData p B j) (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ)
    (i : Fin 2) (xi xnext : D.M) (a : B)
    (hcrit : D.varpi (γ i) = D.verschiebung xi)
    (hnext : D.varpi (γ (i + 1)) = WittVector.teichmuller p a • γ i + D.verschiebung xnext)
    (m : D.M) (hm : m ∈ D.piece i) (hinv : D.varpi m = D.verschiebung m) :
    ∃ (c d b : B) (m₂ x' : D.M),
      m = WittVector.teichmuller p c • γ i +
        D.verschiebung (WittVector.teichmuller p d • γ (i + 1) + D.verschiebung m₂) ∧
      xi = WittVector.teichmuller p b • γ i + D.verschiebung x' ∧
      c = b * c ^ p + a * d := by sorry
