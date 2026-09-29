-- Prove2me | Theorems.Thm_AddSubgroup_inZeroComponentAt_of_cyclic_stable_scalar_dichotomy
-- name    : AddSubgroup.inZeroComponentAt_of_cyclic_stable_scalar_dichotomy
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/11b8e47f-dc77-545e-a16a-89297e2201c7
-- title:
--   Cyclic σ-stable p^m-subgroup with non-±1 scalar is the toric subgroup
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$, let $p$ be a prime and $m \ge 1$, and write $E$ for the base change of $W$ to $\overline{\mathbb{Q}}$ (via $\mathbb{Z} \to \mathbb{Q}$), with $E(\overline{\mathbb{Q}})$ its group of affine points. Assume the $p^m$-torsion submodule of $E(\overline{\mathbb{Q}})$ has exactly $p^{2m}$ elements. Let $K \le E(\overline{\mathbb{Q}})$ be an additive subgroup with $\mathrm{card}\,K = p^m$, cyclic, and killed by $p^m$, and let $\sigma$ be a $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}}$ with $\sigma \cdot x \in K$ for all $x \in K$. Suppose $c \in \mathbb{Z}/p$ satisfies $c \ne 1$, $c \ne -1$ and $\sigma \cdot x = c.\mathrm{val} \cdot x$ for every $x \in K$ with $p \cdot x = 0$. Write `W.InZeroComponentAt A P` for: $P = 0$, or $P = (x,y)$ is an affine nonsingular point with $x \notin A$, or with $x, y \in A$ whose residues give a nonsingular point of the reduction of $W$ over the residue field of $A$. Assume: for every $x \in K$ not satisfying this predicate, one of $\sigma \cdot x - x$, $\sigma \cdot x + x$ does; the predicate is closed under subtraction among $p^m$-torsion points; and exactly $p$ points $x$ satisfy $p \cdot x = 0$ together with the predicate. Then every element of $K$ satisfies the predicate, and conversely every $x$ with $p^m \cdot x = 0$ satisfying it lies in $K$.
--
--   This is the finite-level algebraic form of the identity-component (toricity) argument: under a scalar action by $c \not\equiv \pm 1$ and a fix-or-swap dichotomy, the cyclic $\sigma$-stable subgroup $K$ coincides with the intersection of the $p^m$-torsion with the locus of points reducing into the smooth part at $A$. It is applied in [`FreyPackage.frey_no_cofixed_large`](thm.html#FreyPackage.frey_no_cofixed_large), where $\sigma$ is a Frobenius element at a bad place of the Frey curve; the proof invokes [`IsAddCyclic.of_card_torsion_le_of_exponent_dvd_pow`](thm.html#IsAddCyclic.of_card_torsion_le_of_exponent_dvd_pow) to identify the group of $p^m$-torsion points in the zero component as cyclic of order dividing $p^m$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddSubgroup_inZeroComponentAt_of_cyclic_stable_scalar_dichotomy.lean

import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring

theorem AddSubgroup.inZeroComponentAt_of_cyclic_stable_scalar_dichotomy
    (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))
    (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : 1 ≤ m)
    (hcard : Nat.card (Submodule.torsionBy ℤ
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ((p ^ m : ℕ) : ℤ))
      = p ^ (2 * m))
    (K : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hKcard : Nat.card K = p ^ m) (hK1 : IsAddCyclic K)
    (hKtors : ∀ x ∈ K, p ^ m • x = 0)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hKstab : ∀ x ∈ K, σ • x ∈ K)
    {c : ZMod p} (hc1 : c ≠ 1) (hc1' : c ≠ -1)
    (hscal : ∀ x ∈ K, p • x = 0 → σ • x = c.val • x)
    (hDich : ∀ x ∈ K, ¬ W.InZeroComponentAt A x →
      W.InZeroComponentAt A (σ • x - x) ∨ W.InZeroComponentAt A (σ • x + x))
    (hZeroSub : ∀ x y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      p ^ m • x = 0 → p ^ m • y = 0 →
      W.InZeroComponentAt A x → W.InZeroComponentAt A y → W.InZeroComponentAt A (x - y))
    (hM : Nat.card
      {x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point //
        p • x = 0 ∧ W.InZeroComponentAt A x} = p) :
    (∀ x ∈ K, W.InZeroComponentAt A x) ∧
      ∀ x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
        p ^ m • x = 0 → W.InZeroComponentAt A x → x ∈ K := by sorry
