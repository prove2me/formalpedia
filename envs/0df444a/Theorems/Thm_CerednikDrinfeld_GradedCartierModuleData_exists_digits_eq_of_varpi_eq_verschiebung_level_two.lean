-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_digits_eq_of_varpi_eq_verschiebung_level_two
-- name    : CerednikDrinfeld.GradedCartierModuleData.exists_digits_eq_of_varpi_eq_verschiebung_level_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/ed11fbae-d69a-5539-9434-8e68d817396d
-- title:
--   Level-two digit recursion for varpi = V invariants
-- statement:
--   Fix a prime $p$, a commutative ring $B$ and a ring homomorphism $j : W(\mathbb{F}_{p^2}) \to B$, and let $D$ be a graded Cartier module datum for these data: a module $M$ over the Witt vectors $W(B)$ equipped with additive endomorphisms $F$ (`frobenius`) and $V$ (`verschiebung`), a $W(B)$-linear endomorphism $\varpi$ (`varpi`) and two complementary $W(B)$-submodules $M_0, M_1$ (`piece`), subject to $F(wx) = F(w)F(x)$, $wV(x) = V(F(w)x)$, $V(wF(x)) = V(w)\,x$, $FV = p$, $\varpi V = V\varpi$, $\varpi F = F\varpi$, $\varpi^2 = p$, and to the requirement that $F$, $V$ and $\varpi$ carry $M_i$ into $M_{i+1}$. Let $\gamma_0, \gamma_1$ be a homogeneous $V$-basis, i.e. $\gamma_i \in M_i$ and every $x \in M$ is uniquely of the form $\sum_i [c_i]\gamma_i + V y$ with $c_i \in B$, $y \in M$, where $[\,\cdot\,]$ denotes the Teichmüller lift. Assume $i \in \{0,1\}$ and $a \in B$, $x_i, x_{\mathrm{next}} \in M$ satisfy $\varpi(\gamma_i) = V x_i$ and $\varpi(\gamma_{i+1}) = [a]\gamma_i + V x_{\mathrm{next}}$. Then for every $m \in M_i$ with $\varpi m = V m$ there exist $c,d,e,h,g,k \in B$, elements $m_2, x', x'', x_n', f' \in M$ and $\omega \in W(B)$ such that $m = [c]\gamma_i + V([d]\gamma_{i+1} + V m_2)$, $x_i = [e]\gamma_i + V x'$, $x' = [h]\gamma_{i+1} + V x''$, $x_{\mathrm{next}} = [g]\gamma_{i+1} + V x_n'$, $F(\gamma_i) = [k]\gamma_{i+1} + V f'$, $\omega = [c^p e] + [d a] - [c]$ with $\omega_0 = 0$, and the two digit identities $c = e\,c^p + a\,d$ and $d = g\,d^p + h\,c^{p^2} + \omega_1 k$ hold.
--
--   This is the first- and second-order part of the digit recursion satisfied by $\varpi = V$ invariant elements of a graded Cartier module in a homogeneous $V$-basis, at an index where the structure constant of $\varpi$ vanishes, as in the Cartier–Dieudonné analysis of special formal $\mathcal{O}_D$-modules of Boutot–Carayol; the absence of contributions from deeper digits in the second equation reflects that vanishing. It is used in the dual-number (first-order) study of the tangent behaviour of such invariants for formal $\mathcal{O}_D$-modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_exists_digits_eq_of_varpi_eq_verschiebung_level_two.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.GradedCartierModuleData.exists_digits_eq_of_varpi_eq_verschiebung_level_two
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : Zp2 p →+* B)
    (D : GradedCartierModuleData p B j) (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ)
    (i : Fin 2) (xi xnext : D.M) (a : B)
    (hcrit : D.varpi (γ i) = D.verschiebung xi)
    (hnext : D.varpi (γ (i + 1)) = WittVector.teichmuller p a • γ i + D.verschiebung xnext)
    (m : D.M) (hm : m ∈ D.piece i) (hinv : D.varpi m = D.verschiebung m) :
    ∃ (c d e h g k : B) (m₂ x' x'' xn' fr' : D.M) (ω : WittVector p B),
      m = WittVector.teichmuller p c • γ i +
        D.verschiebung (WittVector.teichmuller p d • γ (i + 1) + D.verschiebung m₂) ∧
      xi = WittVector.teichmuller p e • γ i + D.verschiebung x' ∧
      x' = WittVector.teichmuller p h • γ (i + 1) + D.verschiebung x'' ∧
      xnext = WittVector.teichmuller p g • γ (i + 1) + D.verschiebung xn' ∧
      D.frobenius (γ i) = WittVector.teichmuller p k • γ (i + 1) + D.verschiebung fr' ∧
      ω = WittVector.teichmuller p (c ^ p * e) + WittVector.teichmuller p (d * a) - WittVector.teichmuller p c ∧
      ω.coeff 0 = 0 ∧
      c = e * c ^ p + a * d ∧
      d = g * d ^ p + h * c ^ (p * p) + ω.coeff 1 * k := by sorry
