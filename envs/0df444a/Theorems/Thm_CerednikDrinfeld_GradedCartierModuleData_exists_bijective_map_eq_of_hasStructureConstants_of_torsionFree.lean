-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_bijective_map_eq_of_hasStructureConstants_of_torsionFree
-- name    : CerednikDrinfeld.GradedCartierModuleData.exists_bijective_map_eq_of_hasStructureConstants_of_torsionFree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/0f02a5fd-37f3-52c0-8134-1a07119290ce
-- title:
--   Special Cartier module data with equal structure constants are isomorphic
-- statement:
--   Fix a prime $p$, a commutative ring $B$ in which multiplication by $p$ is injective (every $b$ with $pb=0$ vanishes), and a ring homomorphism $j\colon W(\mathbb{F}_{p^2})\to B$, where [`CerednikDrinfeld.Zp2 p`](def/CerednikDrinfeld_SpecialFormalModule.html#L17) is $W(\mathbb{F}_{p^2})$. Let $D$ and $D'$ be graded Cartier module data over $(B,j)$: each consists of a $W(B)$-module $M$, additive endomorphisms $F$ (`frobenius`) and $V$ (`verschiebung`), a $W(B)$-linear $\Pi$ (`varpi`), and two $W(B)$-submodules `piece 0`, `piece 1` forming a complementary pair, subject to $F(wx)=F(w)F(x)$, $wV(x)=V(F(w)x)$, $V(wF(x))=V(w)x$, $F(V(x))=px$, $\Pi V=V\Pi$, $\Pi F=F\Pi$, $\Pi^2=p$, and the requirement that $V$, $F$ and $\Pi$ each carry `piece i` into `piece (i+1)`. Assume both $D$ and $D'$ are special, i.e. admit a homogeneous $V$-basis and are $V$-adically complete (every sequence $x\colon\mathbb{N}\to M$ has a unique $s$ with $s\equiv\sum_{m<N}V^m(x_m)$ modulo $V^N M$ for all $N$). Let $\gamma\colon \mathrm{Fin}\,2\to D.M$ and $\gamma'\colon \mathrm{Fin}\,2\to D'.M$ be homogeneous $V$-bases, so $\gamma_i\in$ `piece i` and every element is uniquely $\sum_i[c_i]\gamma_i+V(y)$ with $c\in B^2$, $y$ in the module, and similarly for $\gamma'$; and let $a\colon\mathbb{N}\to\mathrm{Fin}\,2\to B$ be a common family of structure constants for both, i.e. for each $i$ and each $N$ one has $\Pi(\gamma_i)\equiv\sum_{m<N}V^m([a_{m,i}]\gamma_{\pi(m,i)})$ modulo $V^N$ applied to some element, where $\pi(m,i)=(m+i+1)\bmod 2$, and likewise for $\gamma'$, $a$. Then there is an additive map $g\colon D.M\to D'.M$ with $g(\gamma_i)=\gamma'_i$ for both $i$, which is bijective, $W(B)$-linear, commutes with $F$, with $V$ and with $\Pi$, and sends `piece i` into `piece i` for each $i$.
--
--   This is the uniqueness half of the classification of special formal modules by their structure constants in the Čerednik–Drinfeld theory: two special graded Cartier module data with homogeneous $V$-bases having the same structure constants are isomorphic as graded Cartier modules. It is used in the construction of a special formal $\mathcal{O}_D$-module realising prescribed data, [`CerednikDrinfeld.GradedCartierModuleData.exists_formalODModule_bijective_of_isSpecialCartierModule_of_torsionFree`](thm.html#CerednikDrinfeld.GradedCartierModuleData.exists_formalODModule_bijective_of_isSpecialCartierModule_of_torsionFree). The hypotheses $hD$, $hD'$ supply $V$-adic completeness, the existence of a homogeneous $V$-basis being already given by $\gamma$ and $\gamma'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_exists_bijective_map_eq_of_hasStructureConstants_of_torsionFree.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.exists_bijective_map_eq_of_hasStructureConstants_of_torsionFree
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (hB : ∀ b : B, (p : B) * b = 0 → b = 0)
    (D D' : CerednikDrinfeld.GradedCartierModuleData p B j)
    (hD : D.IsSpecialCartierModule) (hD' : D'.IsSpecialCartierModule)
    (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ)
    (γ' : Fin 2 → D'.M) (hγ' : D'.IsHomogeneousVBasis γ')
    (a : ℕ → Fin 2 → B) (ha : D.HasStructureConstants γ a) (ha' : D'.HasStructureConstants γ' a) :
    ∃ g : D.M →+ D'.M, (∀ i, g (γ i) = γ' i) ∧
      Function.Bijective g ∧
      (∀ (w : WittVector p B) (x : D.M), g (w • x) = w • g x) ∧
      (∀ x, g (D.frobenius x) = D'.frobenius (g x)) ∧
      (∀ x, g (D.verschiebung x) = D'.verschiebung (g x)) ∧
      (∀ x, g (D.varpi x) = D'.varpi (g x)) ∧
      (∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → g x ∈ D'.piece i) := by sorry
