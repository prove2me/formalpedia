-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_tangent_mem_lieZero_and_lieOne_of_mem_gradedPiece_of_isNilpotent
-- name    : CerednikDrinfeld.FormalODModule.tangent_mem_lieZero_and_lieOne_of_mem_gradedPiece_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/1f2716ca-89f2-553c-9d98-0e73e5e23e55
-- title:
--   Tangent map sends Cartier graded pieces into Lie pieces
-- statement:
--   Fix a prime $p$ and a commutative ring $B$ (of arbitrary universe), together with a ring homomorphism $j$ from $\mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2})$, realised as [`CerednikDrinfeld.Zp2 p`](def/CerednikDrinfeld_SpecialFormalModule.html#L17) $=$ `WittVector p (GaloisField p 2)`, to $B$, and assume that the image of $p$ in $B$ is nilpotent. Let $X$ be a formal $\mathcal{O}_D$-module over $B$ in the sense of `FormalODModule`: a two-dimensional commutative formal group law $X.F$ over $B$ equipped with an action `act` of $\mathbb{Z}_{p^2}$ and a series `varpi`, all by endomorphisms of $X.F$, with `act` unital, multiplicative for composition, additive for the group law, and $\varpi\circ\varpi = \mathrm{act}(p)$, $\varpi\circ\mathrm{act}(a) = \mathrm{act}(Fa)\circ\varpi$. The assertion is the conjunction of two statements. First, every $f$ in the graded piece `X.gradedPiece j 0`, that is every element $f$ of the Cartier module `CartierModule p X.F` satisfying $(\mathrm{act}[c])_{*}f = \langle j([c])\rangle f$ for all $c \in \mathbb{F}_{p^2}$ (Teichmüller representatives $[c]$, the right-hand side being the homothety by $j([c])^{p^0}$), has tangent vector [`MvFormalGroup.CartierModule.tangent f`](def/MvFormalGroup_CartierModule.html#L1037) — the tuple of coefficients of the first variable in the two component power series of $f$ — lying in `X.lieZero j`, the intersection over all $a \in \mathbb{Z}_{p^2}$ of the kernels of $\mathrm{d}\,\mathrm{act}(a) - j(a)\cdot\mathrm{id}$ on $\mathrm{Lie}\,X$. Second, every $f$ in `X.gradedPiece j 1`, i.e. with $(\mathrm{act}[c])_{*}f = \langle j([c])^{p}\rangle f$ for all $c$, has tangent vector in `X.lieOne j`, the intersection over all $a$ of the kernels of $\mathrm{d}\,\mathrm{act}(a) - j(Fa)\cdot\mathrm{id}$, where $F$ is the Witt vector Frobenius.
--
--   This is the statement that the grading of the Cartier module by the $\mathbb{F}_{p^2}$-action descends, via $M \mapsto M/VM = \mathrm{Lie}\,X$, to the corresponding eigenspace decomposition of the tangent space, as in Boutot–Carayol's treatment of special formal $\mathcal{O}_D$-modules. It is used downstream in the analysis of critical charts and of $\eta$-sections attached to edges, where tangent vectors of graded Cartier elements must be recognised as eigenvectors for the full $\mathbb{Z}_{p^2}$-action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_tangent_mem_lieZero_and_lieOne_of_mem_gradedPiece_of_isNilpotent.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.tangent_mem_lieZero_and_lieOne_of_mem_gradedPiece_of_isNilpotent
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (hB : IsNilpotent (p : B)) (X : CerednikDrinfeld.FormalODModule p B) :
    (∀ f ∈ X.gradedPiece j 0, MvFormalGroup.CartierModule.tangent f ∈ X.lieZero j) ∧
    (∀ f ∈ X.gradedPiece j 1, MvFormalGroup.CartierModule.tangent f ∈ X.lieOne j) := by sorry
