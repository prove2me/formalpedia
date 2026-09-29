-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder
-- name    : CerednikDrinfeld.Omega.exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/54682545-28ca-5517-aef9-455dd6374c92
-- title:
--   Valuation current of an automorphic unit as a weighted cycle
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K_0$, let $\varpi\in R$ be irreducible with $R/(\varpi)$ finite, and let $K$ be a complete, algebraically closed extension field of $K_0$ carrying a valuation $v$ with values in $\Gamma_0$, subject to: every element of $R$ has $v\le 1$; every $a\in K_0$ with $v(a)\le 1$ lies in the image of $R$; the powers $v(\varpi)^N$ are cofinal in $\Gamma_0\setminus\{0\}$; and for $v(x)<1$, $y\ne 0$ some $v(x)^n\le v(y)$. Let $\varpi_1$ be a pseudo-uniformiser ($0<v(\varpi_1)<1$ together with the scaling condition) whose affinoids $\mathrm{affinoid}\,\varpi_1\,n$ exhaust $\Omega=K\setminus\mathrm{im}(K_0)$. Let $G$ be a group with $\rho:G\to \mathrm{PGL}_2(K_0)$ injective, acting on the vertices of the Bruhat–Tits tree of $R$ over $K_0$ through $\rho$ and preserving adjacency, with all vertex stabilisers finite and finitely many vertex orbits, and let $\tau$ be a $G$-invariant $2$-colouring taking distinct values on adjacent vertices. Let $E$ be a finite type equipped with an equivalence $eE$ onto the set of $G$-orbits of darts $e$ with $\tau(e.\mathrm{out}.\mathrm{fst})=0$. Let $f$ be a unit of the ring $\mathrm{holRing}\,\varpi_1$ of functions $\Omega\to K$ holomorphic on every affinoid, satisfying $f(\rho(\gamma)\cdot z)=\chi(\gamma)f(z)$ for a character $\chi:G\to K^\times$ that is trivial on every element of finite order, and assume tameness: $v$ of the cardinality of each vertex stabiliser, viewed in $K$, equals $1$. Then there exists $c:E\to\mathbb Z$ lying in the ribbon kernel (the intersection of the kernels of the maps $\mathrm{jointDelta}$) of the degeneracy data on $E$ with vertex set the set of $G$-orbits of vertices, source and target of $e$ the orbits of $eE(e).\mathrm{out}.\mathrm{fst}$ and $eE(e).\mathrm{out}.\mathrm{snd}$ and all weights $1$, such that for every $g\in \mathrm{GL}_2(K_0)$, every walk $p$ in the tree from the standard vertex to $g\cdot$(standard vertex), and all $w,w'\in \mathrm{affinoid}\,\varpi_1\,0$, $$v\bigl(f(\overline{g}\cdot w)\bigr)=v\bigl(f(w')\bigr)\cdot v(\varpi)^{\sum_{e} \mathrm{stabWidth}(eE(e))\,c(e)\,\mathrm{walkCycle}(p)(e)},$$ where $\overline g$ is the image of $g$ in $\mathrm{PGL}_2(K_0)$, $\mathrm{stabWidth}$ of a dart orbit is the cardinality of the stabiliser of its chosen representative and $\mathrm{walkCycle}(p)(e)$ is the signed number of times $p$ crosses darts of the orbit $eE(e)$; and if $c=0$ then $v\circ f$ takes the same value at all points of $\Omega$.
--
--   This is the computation of the valuation current of an automorphic unit on Drinfel'd's upper half plane for a tame cocompact tree lattice, in the form of Kurihara's weighted dual graph: the current along a dart of orbit $e$ is the stabiliser order of $e$ times an unweighted cycle $c$ of the finite quotient graph (in the Schottky case all stabilisers are trivial). It feeds the extraction of the multiplicative periods of such a unit in [`CerednikDrinfeld.Omega.exists_forall_eq_period_of_isUnit_of_apply_smul_eq_mul_of_forall_isOfFinOrder`](thm.html#CerednikDrinfeld.Omega.exists_forall_eq_period_of_isUnit_of_apply_smul_eq_mul_of_forall_isOfFinOrder).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.GroupTheory.OrderOfElement

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Omega.exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (ϖ₁ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ₁)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    [MulAction G (LT.LatticeTree.Vertex R K₀)] [GraphAction G (BruhatTits.tree R K₀)]
    (hρ : ActsThrough (LT.LatticeTree.Vertex R K₀) ρ) (hρinj : Function.Injective ρ)
    (hfin : ∀ w : LT.LatticeTree.Vertex R K₀, Finite (MulAction.stabilizer G w))
    [Finite (QuotVert G (LT.LatticeTree.Vertex R K₀))]
    (τ : LT.LatticeTree.Vertex R K₀ → ZMod 2) (hτ : ∀ (g : G) (w : LT.LatticeTree.Vertex R K₀), τ (g • w) = τ w)
    (hadj : ∀ u w : LT.LatticeTree.Vertex R K₀, (BruhatTits.tree R K₀).Adj u w → τ u ≠ τ w)
    [DecidableEq (QuotEdge G (BruhatTits.tree R K₀))] [DecidableEq (QuotVert G (LT.LatticeTree.Vertex R K₀))]
    {E : Type} [Fintype E] (eE : E ≃ {e : QuotEdge G (BruhatTits.tree R K₀) // τ e.out.fst = 0})
    (f : ↥(holRing ϖ₁)) (hf : IsUnit f) (χ : G →* Kˣ)
    (haut : ∀ (γ : G) (z : ↥(upperHalfPlane K₀ K)),
      (f : ↥(upperHalfPlane K₀ K) → K) ((ρ γ) • z) = ((χ γ : Kˣ) : K) * (f : ↥(upperHalfPlane K₀ K) → K) z)
    (hχ : ∀ γ : G, IsOfFinOrder γ → χ γ = 1)

    (htame : ∀ w : LT.LatticeTree.Vertex R K₀, Valued.v ((Nat.card ↥(MulAction.stabilizer G w) : ℕ) : K) = 1) :
    ∃ c : E → ℤ,
      c ∈ ribbonKernel
        (⟨fun e => Quotient.mk (orbitRel G (LT.LatticeTree.Vertex R K₀)) (eE e).1.out.fst,
          fun e => Quotient.mk (orbitRel G (LT.LatticeTree.Vertex R K₀)) (eE e).1.out.snd,
          fun _ => 1⟩ : DegeneracyData E (QuotVert G (LT.LatticeTree.Vertex R K₀))) ∧
      (∀ (g : GL (Fin 2) K₀)
        (p : (BruhatTits.tree R K₀).Walk (LT.LatticeTree.stdVertex R K₀) (g • LT.LatticeTree.stdVertex R K₀))
        (w w' : K) (hw : w ∈ affinoid ϖ₁ 0) (hw' : w' ∈ affinoid ϖ₁ 0),
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K)
            ((Matrix.ProjGenLinGroup.mk g) • ⟨w, affinoid_subset_upperHalfPlane ϖ₁ 0 hw⟩)) =
          Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) ⟨w', affinoid_subset_upperHalfPlane ϖ₁ 0 hw'⟩) *
            Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^
              (∑ e, ((stabWidth G (BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) * c e *
                walkCycle (BruhatTits.tree R K₀) (fun e => (eE e).1) p e)) ∧
      (c = 0 → ∀ z w : ↥(upperHalfPlane K₀ K),
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) = Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) w)) := by sorry
