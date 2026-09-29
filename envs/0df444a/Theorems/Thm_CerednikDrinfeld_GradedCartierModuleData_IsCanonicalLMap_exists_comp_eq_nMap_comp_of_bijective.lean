-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_exists_comp_eq_nMap_comp_of_bijective
-- name    : CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.exists_comp_eq_nMap_comp_of_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/31b112da-6f64-5e3e-b802-c61d66ad14b6
-- title:
--   Canonical L-maps transport along isomorphisms of graded Cartier data
-- statement:
--   Fix a prime $p$, a commutative ring $B$ and a ring homomorphism $j \colon W(\mathbb{F}_{p^2}) \to B$, and let $D$, $D'$ be graded Cartier module data over $(p, B, j)$, so each consists of a $W(B)$-module $M$ with additive endomorphisms $F$, $V$, a $W(B)$-linear $\varpi$ and a pair of complementary submodules $\mathrm{piece}\,0$, $\mathrm{piece}\,1$ satisfying the usual Cartier identities and the shift conditions. Assume $D$ is a special Cartier module (it admits a homogeneous $V$-basis and is $V$-adically complete), and let $f \colon D.M \to D'.M$ be an additive map which is bijective, satisfies $f(w \cdot x) = w \cdot f(x)$ for all $w \in W(B)$, commutes with $F$, with $V$ and with $\varpi$, and sends $\mathrm{piece}\,i$ into $\mathrm{piece}\,i$ for $i \in \{0,1\}$. Let $L \colon D.M \to D.\mathrm{NMod}$ be a canonical $L$-map, that is, a Cartier $L$-map ($L(w\cdot x) = \sigma(w)\cdot L(x)$, $L(Vx) = \mathrm{nMk}(\varpi x, 0)$, $\lambda \circ L = F$) which, over some surjection $\varphi \colon S \to B$ from a ring without $p$-torsion, is the base change of a Cartier $L$-map on a special datum over $S$. Then there is an additive $L' \colon D'.M \to D'.\mathrm{NMod}$ which is again a canonical $L$-map and satisfies $L'(f(x)) = (\mathrm{nMap}\,f)(L(x))$ for all $x \in D.M$, where $\mathrm{nMap}\,f$ is the map $D.\mathrm{NMod} \to D'.\mathrm{NMod}$ induced by $f$.
--
--   This is the transport of the canonical $L$-map datum along an isomorphism of graded Cartier module data, in the form used in the Čerednik–Drinfeld theory of special formal $\mathcal{O}_D$-modules. It feeds the results on Cartier quadruples attached to rigidified special formal modules, where a quadruple is produced from an isomorphic one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_exists_comp_eq_nMap_comp_of_bijective.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.exists_comp_eq_nMap_comp_of_bijective
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (D D' : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (f : D.M →+ D'.M) (hf : Function.Bijective f)
    (hW : ∀ (w : WittVector p B) (x : D.M), f (w • x) = w • f x)
    (hF : ∀ x, f (D.frobenius x) = D'.frobenius (f x))
    (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x))
    (hpc : ∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → f x ∈ D'.piece i)
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L) :
    ∃ L' : D'.M →+ D'.NMod, D'.IsCanonicalLMap L' ∧
      ∀ x : D.M, L' (f x) = D.nMap D' f hV hPi (L x) := by sorry
