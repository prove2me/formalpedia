-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_eq_varpi_add_verschiebung_iff_dvd_of_varpi_eq_teichmuller_smul_add
-- name    : CerednikDrinfeld.GradedCartierModuleData.exists_eq_varpi_add_verschiebung_iff_dvd_of_varpi_eq_teichmuller_smul_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/b19f1471-1b1a-5fa1-afa0-bb82f1931033
-- title:
--   Divisibility criterion for [c]γᵢ + Vn ∈ Pi Mᵢ₊₁ + VM
-- statement:
--   Fix a prime $p$, a commutative ring $B$ and a ring homomorphism $j \colon W(\mathbf{F}_{p^2}) \to B$, and let $D$ be a graded Cartier module datum over $(B,j)$: a module $M$ over the Witt ring $W(B)$ equipped with additive endomorphisms $F$ (`frobenius`) and $V$ (`verschiebung`) and a $W(B)$-linear endomorphism $\Pi$ (`varpi`) satisfying $F(wx) = F(w)F(x)$, $wV(x) = V(F(w)x)$, $V(wF(x)) = V(w)x$, $F(V(x)) = px$, $\Pi V = V\Pi$, $\Pi F = F\Pi$ and $\Pi^2 = p$, together with two $W(B)$-submodules `piece 0`, `piece 1` that are complementary in $M$ and are permuted cyclically by $V$, $F$ and $\Pi$ in the sense that each of these maps `piece i` into `piece (i+1)`. Let $\gamma \colon \mathrm{Fin}\,2 \to M$ be a homogeneous $V$-basis, i.e. $\gamma_i \in$ `piece i` for both $i$ and every $x \in M$ has a unique expression $x = \sum_i [c_i]\gamma_i + V y$ with $c \colon \mathrm{Fin}\,2 \to B$ and $y \in M$, where $[\,\cdot\,]$ denotes the Teichmüller lift $B \to W(B)$. Fix $i \in \mathrm{Fin}\,2$, an element $x_{i+1} \in M$ and $a \in B$ with $\Pi \gamma_{i+1} = [a]\gamma_i + V x_{i+1}$. Then for all $c \in B$ and $n \in M$ the element $[c]\gamma_i + Vn$ lies in $\Pi(\mathrm{piece}\,(i+1)) + V M$, that is, there exist $x \in$ `piece (i+1)` and $x' \in M$ with $[c]\gamma_i + Vn = \Pi x + V x'$, if and only if $a$ divides $c$ in $B$.
--
--   This is the leading-digit criterion in the Cartier-theoretic description of special formal $O_D$-modules underlying the Čerednik–Drinfeld uniformisation: membership of a degree-$i$ element in $\Pi M_{i+1} + VM$ is read off from divisibility of its Teichmüller leading coefficient by the coefficient $a$ occurring in $\Pi\gamma_{i+1}$. It is used in the two statements about rigidified special formal modules that compare $\Pi$- and $V$-structures with the maps $N$ and $\lambda$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_exists_eq_varpi_add_verschiebung_iff_dvd_of_varpi_eq_teichmuller_smul_add.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.GradedCartierModuleData.exists_eq_varpi_add_verschiebung_iff_dvd_of_varpi_eq_teichmuller_smul_add
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : Zp2 p →+* B)
    (D : GradedCartierModuleData p B j) (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ)
    (i : Fin 2) (xnext : D.M) (a : B)
    (hnext : D.varpi (γ (i + 1)) = WittVector.teichmuller p a • γ i + D.verschiebung xnext)
    (c : B) (n : D.M) :
    (∃ x ∈ D.piece (i + 1), ∃ x' : D.M,
        WittVector.teichmuller p c • γ i + D.verschiebung n = D.varpi x + D.verschiebung x') ↔ a ∣ c := by sorry
