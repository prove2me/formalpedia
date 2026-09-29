-- Prove2me | Theorems.Thm_AddSubgroup_mem_of_torsion_inZeroComponentAt_of_forall_not_inZeroComponentAt_sub
-- name    : AddSubgroup.mem_of_torsion_inZeroComponentAt_of_forall_not_inZeroComponentAt_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/b8eb650d-ca63-5055-81e0-664c574fe660
-- title:
--   Zero-component p^m-torsion is contained in K
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$, let $p$ be a prime and $m$ a natural number, and write $E := W_{\mathbb{Q}}$ for the base change of $W$ along $\mathbb{Z} \to \mathbb{Q}$, whose points over $\overline{\mathbb{Q}}$ form the group in question. Here a point $P$ satisfies $W.\mathrm{InZeroComponentAt}\ A$ when either $P = 0$, or $P$ is an affine point $(x,y)$ such that either $x \notin A$, or both $x, y \in A$ and the pair of residues of $x$ and $y$ in the residue field of $A$ is a nonsingular point of the reduction of $W$ over that residue field. Assume given a subgroup $K$ of $E(\overline{\mathbb{Q}})$ with $\operatorname{Nat.card} K = p^m$ all of whose elements are killed by $p^m$; a point $e$ with $p \cdot e = 0$; that the $p$-torsion submodule $E(\overline{\mathbb{Q}})[p]$ has cardinality $p^2$; that the above zero-component condition is stable under differences of points killed by $p^m$; and that for every $k \in K$ the point $e - k$ fails the zero-component condition. Then every point $x$ with $p^m \cdot x = 0$ satisfying the zero-component condition at $A$ lies in $K$.
--
--   This is the finite-level form of the second reduction in Mazur's argument: at a place $A$ of $\overline{\mathbb{Q}}$, the existence of a $p$-torsion point $e$ no translate of which meets the zero component forces the whole of $W^0_A \cap E[p^m]$ into the given subgroup $K$ of order $p^m$. It is a purely group-theoretic consequence of the cyclicity criterion [`IsAddCyclic.of_card_torsion_le_of_exponent_dvd_pow`](thm.html#IsAddCyclic.of_card_torsion_le_of_exponent_dvd_pow), and is used in the proof of [`FreyPackage.frey_no_cofixed_large`](thm.html#FreyPackage.frey_no_cofixed_large), the step of the irreducibility argument for Frey curves dealing with bad primes $\ell \equiv \pm 1 \pmod p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddSubgroup_mem_of_torsion_inZeroComponentAt_of_forall_not_inZeroComponentAt_sub.lean

import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring

theorem AddSubgroup.mem_of_torsion_inZeroComponentAt_of_forall_not_inZeroComponentAt_sub
    (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))
    (p : ℕ) [Fact p.Prime] (m : ℕ)
    (K : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hKcard : Nat.card K = p ^ m)
    (hKtors : ∀ x ∈ K, p ^ m • x = 0)
    (e : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) (he : p • e = 0)
    (hcard₁ : Nat.card (Submodule.torsionBy ℤ
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point (p : ℤ)) = p ^ 2)
    (hZeroSub : ∀ x y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      p ^ m • x = 0 → p ^ m • y = 0 →
      W.InZeroComponentAt A x → W.InZeroComponentAt A y → W.InZeroComponentAt A (x - y))
    (hStep3 : ∀ k ∈ K, ¬ W.InZeroComponentAt A (e - k)) :
    ∀ x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      p ^ m • x = 0 → W.InZeroComponentAt A x → x ∈ K := by sorry
