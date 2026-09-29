-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_monoidHom_monoidHom_symm_mul_period_eq_one_v_eq_zpow_stabWidth
-- name    : CerednikDrinfeld.Omega.exists_monoidHom_monoidHom_symm_mul_period_eq_one_v_eq_zpow_stabWidth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/21205e52-8f4a-5e2b-9117-f919c9eca4b2
-- title:
--   Stabiliser-weighted period pairing for tree lattices with torsion
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K_0$, let $\varpi\in R$ be irreducible with finite residue ring $R/(\varpi)$, and let $K$ be a complete valued field, with value group $\Gamma_0$, extending $K_0$, subject to: every element of $R$ has image of valuation $\le 1$ in $K$ (`hint`), every $a\in K_0$ whose image has valuation $\le 1$ lies in the image of $R$ (`hv`), and the powers of $v(\varpi)$ are coinitial in $\Gamma_0\setminus\{0\}$ (`hq`). Let $\varpi_1$ be a pseudo-uniformizer, i.e. an element of $K_0$ whose image has valuation in $(0,1)$ and such that the valuation of each nonzero element of $K_0$ is squeezed between $v(\varpi_1)^{N}$ and $v(\varpi_1)^{-N}$ for some $N$, and assume it is exhausting: every point of $K$ outside the image of $K_0$ (the Drinfeld upper half plane) lies in one of the affinoids $\mathrm{affinoid}\ \varpi_1\ n$. Let $G$ be a group with a homomorphism $\rho : G \to \mathrm{PGL}_2(K_0)$, acting on the vertices of the lattice tree of $R$ in $K_0^2$ in a way that preserves adjacency in the Bruhat–Tits tree and that factors through $\rho$ (`hρ`: $g\cdot w = \rho(g)\cdot w$), with all vertex stabilisers finite. Let $\tau$ be a $G$-invariant map from vertices to $\mathbb Z/2$ taking different values on adjacent vertices, let $E$ be a finite type and $eE$ a bijection of $E$ with those $G$-orbits of darts of the tree whose chosen representative has source of colour $0$. Let $g_0,g_a\in \mathrm{GL}_2(K_0)$ and $w_0,w_a$ be points of $\mathrm{affinoid}\ \varpi_1\ 0$ with $\tau(g_0\cdot v_0)\neq\tau(g_a\cdot v_0)$ for the standard vertex $v_0$, put $a=g_a w_a$, $z_0=g_0 w_0$ (images under the Möbius action of the classes of $g_a$, $g_0$), and let $K_p\subseteq K$ be a subfield containing every period $\Theta(a,\rho(\alpha)a;z_0,\rho(\beta)z_0)$. The conclusion: there is a bimultiplicative pairing $Q : G \to G \to K_p^{\times}$ which is symmetric, satisfies $Q(\alpha,\beta)\cdot \Theta(a,\rho(\alpha)a;z_0,\rho(\beta)z_0)=1$ in $K$, and whose valuation is $$v\bigl(Q(\alpha,\beta)\bigr)=v(\varpi)^{\sum_{e\in E} |G_{e}|\,c_\alpha(e)\,c_\beta(e)},$$ an integer power, where $|G_e|$ is `stabWidth`, the cardinality of the stabiliser of the chosen dart representative of the orbit $eE(e)$, and $c_g(e)$ is `pathCycle`, the integer vector attached by `walkCycle` to a chosen walk from $v_0$ to $g\cdot v_0$ along the orbits $eE$ (and $0$ if $g\cdot v_0$ is unreachable from $v_0$).
--
--   This is the Manin–Drinfeld period pairing in the form needed for Mumford curves uniformised by a tree lattice with torsion: the classical Schottky hypothesis is replaced by finiteness of the vertex stabilisers, and the valuation of the pairing is accordingly weighted by the stabiliser widths of the edge orbits of the quotient graph. It is the packaged input for the construction of a period datum on the Jacobian, used by [`AlgebraicCurve.Pic0.exists_periodDatum_Q_mul_period_eq_one_of_mumfordQuotient`](thm.html#AlgebraicCurve.Pic0.exists_periodDatum_Q_mul_period_eq_one_of_mumfordQuotient).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_monoidHom_monoidHom_symm_mul_period_eq_one_v_eq_zpow_stabWidth.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_monoidHom_monoidHom_symm_mul_period_eq_one_v_eq_zpow_stabWidth
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (ϖ₁ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ₁)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    [MulAction G (LT.LatticeTree.Vertex R K₀)]
    [CerednikDrinfeld.Mumford.GraphAction G (CerednikDrinfeld.BruhatTits.tree R K₀)]
    (hρ : CerednikDrinfeld.Mumford.ActsThrough (LT.LatticeTree.Vertex R K₀) ρ)
    (hfin : ∀ w : LT.LatticeTree.Vertex R K₀, Finite (MulAction.stabilizer G w))
    (τ : LT.LatticeTree.Vertex R K₀ → ZMod 2) (hτ : ∀ (g : G) (w : LT.LatticeTree.Vertex R K₀), τ (g • w) = τ w)
    (hadj : ∀ u w : LT.LatticeTree.Vertex R K₀, (CerednikDrinfeld.BruhatTits.tree R K₀).Adj u w → τ u ≠ τ w)
    [DecidableEq (CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀))]
    {E : Type} [Fintype E]
    (eE : E ≃ {e : CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀) // τ e.out.fst = 0})
    (g₀ gₐ : GL (Fin 2) K₀) {w₀ wₐ : K} (hw₀ : w₀ ∈ affinoid ϖ₁ 0) (hwₐ : wₐ ∈ affinoid ϖ₁ 0)
    (hsep : τ (g₀ • LT.LatticeTree.stdVertex R K₀) ≠ τ (gₐ • LT.LatticeTree.stdVertex R K₀))
    (Kp : Subfield K)
    (hKp : ∀ α β : G, period ρ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk gₐ) wₐ)
                              (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₀) w₀) α β ∈ Kp) :
    ∃ Q : G →* G →* (↥Kp)ˣ,
      (∀ α β : G, Q α β = Q β α) ∧
      (∀ α β : G, (((Q α β : (↥Kp)ˣ) : ↥Kp) : K) *
          period ρ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk gₐ) wₐ)
                   (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₀) w₀) α β = 1) ∧
      (∀ α β : G, Valued.v (((Q α β : (↥Kp)ˣ) : ↥Kp) : K) =
          Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^
            (∑ e : E, ((CerednikDrinfeld.Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) *
            CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1)
                (LT.LatticeTree.stdVertex R K₀) α e *
            CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1)
                (LT.LatticeTree.stdVertex R K₀) β e)) := by sorry
