-- Prove2me | Theorems.Thm_CohCarrier_heckeSym_top_of_coprime
-- name    : CohCarrier.heckeSym_top_of_coprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/0b7804d2-39d1-5f53-9eb3-55068bb50e5d
-- title:
--   Upper and lower Hecke operators agree at full level for q coprime to M
-- statement:
--   Let $M$ and $q$ be natural numbers, both nonzero, such that $q$ is coprime to $M$, and let $V$ be an additive commutative group. Take $H = \top$, the full subgroup of $(\mathbb{Z}/M)^\times$, so that `GammaH M ⊤` is the image of $\Gamma_0(M)$ in $\mathrm{SL}(2,\mathbb{Z})$, and `H1 M ⊤ V` is the group of additive homomorphisms from `Additive (GammaH M ⊤)`, i.e. from $\Gamma_0(M)$ written additively, to $V$ (so an element of `H1` is a homomorphism of $\Gamma_0(M)$ into $V$, not a class of inhomogeneous cocycles). Let $F$ be such a homomorphism. Two endomorphisms of `H1 M ⊤ V` are in play: `heckeT M ⊤ q V`, obtained by reading $F$ multiplicatively, precomposing with the group homomorphism `conjL M ⊤ q` from `GammaHUpper M ⊤ q` to `GammaH M ⊤` (conjugation by the matrix `conjUpperMat q`), and applying the transfer map of the subgroup `GammaHUpper M ⊤ q`; and `heckeTlower M ⊤ q V`, defined in exactly the same way with `GammaHLower M ⊤ q` and the conjugation homomorphism `conjLowerL M ⊤ q` (built from `conjLowerMat q`) in place of the upper ones. The assertion is that these two operators have the same value on $F$: `heckeTlower M ⊤ q V F = heckeT M ⊤ q V F`. Primality of $q$ is not assumed, only coprimality to $M$.
--
--   This is the symmetry of the $q$-th Hecke operator at level $\Gamma_0(M)$ with respect to the two standard families of coset representatives, upper- and lower-triangular, for the double coset of $\mathrm{diag}(q,1)$, in the transfer-map formulation used for the cohomology carrier here. It is used in the computation of the corner entries of the degeneracy matrices, in [`CohCarrier.jDeg_iDeg_corner_of_prime_sq`](thm.html#CohCarrier.jDeg_iDeg_corner_of_prime_sq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_heckeSym_top_of_coprime.lean

import Definitions.Def_CohCarrier_Lower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.heckeSym_top_of_coprime (M q : ℕ) [NeZero M] [NeZero q] (hcop : Nat.Coprime q M)
    {V : Type} [AddCommGroup V] (F : H1 M ⊤ V) :
    heckeTlower M ⊤ q V F = heckeT M ⊤ q V F := by sorry
