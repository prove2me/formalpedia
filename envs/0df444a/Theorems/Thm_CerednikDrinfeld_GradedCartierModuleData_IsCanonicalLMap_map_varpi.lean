-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_map_varpi
-- name    : CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.map_varpi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/60b9b3b2-4cdd-5bd1-ba86-f95af4f40331
-- title:
--   Canonical L-maps commute with Pi
-- statement:
--   Fix a prime $p$, a commutative ring $B$ and a ring homomorphism $j \colon \mathbb{W}(\mathbb{F}_{p^2}) \to B$ (here `Zp2 p` is the ring of Witt vectors of the field with $p^2$ elements), and let $D$ be a graded Cartier module datum over $(B,j)$: a $\mathbb{W}(B)$-module `D.M` with additive endomorphisms $F$ (`frobenius`) and $V$ (`verschiebung`), a $\mathbb{W}(B)$-linear $\Pi$ (`varpi`) with $\Pi V = V\Pi$, $\Pi F = F\Pi$ and $\Pi^2 = p$, and a pair of complementary submodules `piece 0`, `piece 1` each shifted by $F$, $V$ and $\Pi$, subject to the usual Frobenius/Verschiebung semilinearity and $FV = p$. Assume `D.IsSpecialCartierModule`, i.e. `D.M` admits a homogeneous $V$-basis $(\gamma_0,\gamma_1)$ and is $V$-adically complete in the sense that every sequence of elements sums uniquely in the $V$-adic sense. Let $L \colon$ `D.M` $\to$ `D.NMod` be additive, where `D.NMod` is the quotient of `D.M` $\times$ `D.Sigma` by the submodule `D.nRel`, and assume `D.IsCanonicalLMap L`: $L$ is a Cartier $L$-map ($L(w\cdot x) = F(w)\cdot L(x)$, $L(Vx)$ is the class of $(\Pi x,0)$, and `lambda` $\circ\, L = F$), and moreover $L$ descends from a lift, namely there are a commutative ring $S$ with structure map $j_S$, a surjection $\varphi \colon S \to B$ whose source has no $p$-torsion, a special graded Cartier module datum $D_\ell$ over $(S,j_S)$, an additive $f \colon D_\ell.M \to D.M$ which is a base change along $\varphi$ (Witt-semilinear, commuting with $F$, $V$ and $\Pi$, preserving the pieces, and carrying some homogeneous $V$-basis to one), and a Cartier $L$-map $L_\ell$ on $D_\ell$ with $L \circ f =$ `nMap` $f \circ L_\ell$. Then for every $x \in$ `D.M` one has $L(\Pi x) =$ `D.nVarpi` $(L x)$, where `nVarpi` is the endomorphism of `D.NMod` induced by $\Pi$ on both coordinates.
--
--   This is the statement that a canonical $L$-map is compatible with the action of the uniformiser $\Pi$ of the quaternion order, so that $L$ is $\mathcal{O}_D[\Pi]$-linear (Boutot–Carayol II (3.8)–(3.9)). It is used in the study of $\eta$-sections and rigidifications of special formal modules, for instance in the results on $\Pi$-stability of $\eta(L)$ and on tangent germs of rigidified special formal modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_map_varpi.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.map_varpi
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L) (x : D.M) :
    L (D.varpi x) = D.nVarpi (L x) := by sorry
