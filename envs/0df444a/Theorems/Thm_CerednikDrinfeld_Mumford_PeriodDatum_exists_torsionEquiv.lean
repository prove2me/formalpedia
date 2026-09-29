-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_PeriodDatum_exists_torsionEquiv
-- name    : CerednikDrinfeld.Mumford.PeriodDatum.exists_torsionEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/b2443049-68c4-53eb-918b-d17ea23676f8
-- title:
--   p-torsion of a period datum's uniformising group
-- statement:
--   Let $E$ be a finite type and $V$ a type with decidable equality, and let $D$ be a degeneracy datum on them, i.e. two maps $a,b \colon E \to V$ together with widths $w \colon E \to \mathbb{N}_{>0}$; write $Z =$ `ribbonKernel D` for the submodule of $(E \to \mathbb{Z})$ cut out as the intersection of the kernels of the pushforwards along $a$ and along $b$. Let $K \subseteq L$ be fields ($L$ a $K$-algebra) and $ord \colon \mathrm{Additive}\,K^\times \to \mathbb{Z}$ an additive homomorphism, and let $P$ be a period datum for $D$ over $(K,L,ord)$: a $\mathbb{Z}$-bilinear pairing $Q$ on $Z$ with values in $\mathrm{Additive}\,K^\times$ which is symmetric and satisfies $ord(Q(x,y)) =$ `ribbonGram D` $(x,y)$, the width pairing restricted to $Z$. Its torus points are the $\mathbb{Z}$-linear maps $Z \to \mathrm{Additive}\,L^\times$, and `P.U` is the submodule of those torus points whose class modulo `P.periodLattice` is a torsion element. Let $p$ be a prime and $\zeta \in L^\times$ a primitive $p$-th root of unity. Then there is a $\mathbb{Z}$-linear isomorphism $e$ from the $p$-torsion submodule $\mathrm{torsionBy}_{\mathbb{Z}}(\mathrm{P.U}, p)$ onto $\mathrm{Hom}_{\mathbb{Z}}(Z, \mathbb{Z}/p)$ such that for every $p$-torsion element $v$ and every $z \in Z$, the value at $z$ of the torus point underlying $v$ is $\zeta^{\,(e(v)(z)).\mathrm{val}}$, the exponent being the representative of $e(v)(z)$ in $\{0,\dots,p-1\}$.
--
--   This is the toric input to Kummer-theoretic descriptions of $p$-torsion in Mumford uniformisation: the $p$-torsion of the uniformising group of a period datum is canonically the group of $\mathbb{Z}/p$-valued linear forms on the ribbon kernel, the identification being normalised by a chosen primitive $p$-th root of unity. It is used in the construction of the tame character and Kummer law attached to a period uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_PeriodDatum_exists_torsionEquiv.lean

import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve CerednikDrinfeld CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.PeriodDatum.exists_torsionEquiv
    {E V : Type} [Fintype E] [DecidableEq V] {D : DegeneracyData E V}
    {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ}
    (P : PeriodDatum D K L ord) {p : ℕ} [Fact p.Prime] {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p) :
    ∃ e : ↥(Submodule.torsionBy ℤ ↥P.U (p : ℤ)) ≃ₗ[ℤ] (↥(ribbonKernel D) →ₗ[ℤ] ZMod p),
      ∀ (v : ↥(Submodule.torsionBy ℤ ↥P.U (p : ℤ))) (z : ↥(ribbonKernel D)),
        ((v : ↥P.U) : P.TorusPoints) z = Additive.ofMul (ζ ^ (e v z).val) := by sorry
