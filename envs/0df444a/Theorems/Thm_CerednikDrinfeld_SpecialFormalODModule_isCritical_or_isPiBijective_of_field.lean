-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_isCritical_or_isPiBijective_of_field
-- name    : CerednikDrinfeld.SpecialFormalODModule.isCritical_or_isPiBijective_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/2bb5c3be-a4a1-5613-b233-86312b29d342
-- title:
--   Each index critical or Pi-bijective over a field
-- statement:
--   Let $p$ be a prime, $k$ a field of characteristic $p$, and $j\colon W(\mathbb F_{p^2})\to k$ a ring homomorphism, where [`CerednikDrinfeld.Zp2 p`](def/CerednikDrinfeld_SpecialFormalModule.html#L17) is the Witt vector ring of `GaloisField p 2`. Let $\Phi$ be a special formal $\mathcal O_D$-module over $k$ relative to $j$: a two-dimensional commutative formal group law $F$ over $k$ together with an action of $W(\mathbb F_{p^2})$ by endomorphism series and a uniformiser series $\varpi$ with $\varpi\circ\varpi = [p]$ and $\varpi\circ[a] = [\sigma(a)]\circ\varpi$, subject to the condition `IsSpecial` (the two Lie pieces attached to $j$ are complementary and each invertible as a $k$-module) and to `HasHeight 4`. Write $M$ for the Cartier module of $F$, $V$ for its Verschiebung, $\Pi$ for the action of the endomorphism $\varpi$, and $M_n$ for the graded piece `gradedPiece j n`, consisting of those $f$ with $[\omega(c)]f = j(\omega(c))^{p^n}f$ for every $c\in\mathbb F_{p^2}$, $\omega$ the Teichmüller lift. The theorem asserts two things. First, for every $n\in\mathbb N$, either $n$ is critical, i.e. $\Pi m\in VM$ for all $m\in M_n$, or $n$ is $\Pi$-bijective, i.e. for $f\in M_n$ the condition $\Pi f\in VM$ forces $f\in VM$, and every $h\in M_{n+1}$ is of the form $\Pi f+Vg$ with $f\in M_n$ and $g\in M$. Second, at least one of the indices $0$ and $1$ is critical.
--
--   This is the dichotomy of Boutot–Carayol for the Cartier module of a special formal $\mathcal O_D$-module in characteristic $p$: through the tangent map each quotient $M_n/VM_{n-1}$ is a line over $k$, on which $\Pi$ acts linearly, hence by zero or bijectively, and $\Pi^2=p$ forces criticality at one of the two indices. It is the input for the analysis of the graded pieces and of the canonical map $L_M$ used in the Čerednik–Drinfeld uniformisation, and is invoked by the results on $\eta$-pieces and on representations of elements by $\Pi$-monomials over algebraically closed fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormalODModule_isCritical_or_isPiBijective_of_field.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart
import Definitions.Def_CerednikDrinfeld_CartierNModule
import Definitions.Def_CerednikDrinfeld_CartierLMapFibre

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.SpecialFormalODModule.isCritical_or_isPiBijective_of_field
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p]
    (j : CerednikDrinfeld.Zp2 p →+* k) (Φ : CerednikDrinfeld.SpecialFormalODModule p j) :
    (∀ n : ℕ, CerednikDrinfeld.FormalODModule.CritChart.IsCritical Φ.toFormalODModule j n ∨
        Φ.IsPiBijective j n) ∧
      (CerednikDrinfeld.FormalODModule.CritChart.IsCritical Φ.toFormalODModule j 0 ∨
        CerednikDrinfeld.FormalODModule.CritChart.IsCritical Φ.toFormalODModule j 1) := by sorry
