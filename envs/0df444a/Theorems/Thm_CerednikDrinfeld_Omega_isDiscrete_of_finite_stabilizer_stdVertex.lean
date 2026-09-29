-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_isDiscrete_of_finite_stabilizer_stdVertex
-- name    : CerednikDrinfeld.Omega.isDiscrete_of_finite_stabilizer_stdVertex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/215fdccb-979c-5005-ac5e-03c6830c0fcf
-- title:
--   Finite stabiliser of the standard vertex implies discreteness
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain which is a discrete valuation ring) with field of fractions $K_0$, let $\varpi \in R$ be irreducible, and assume the residue ring $R/(\varpi)$ is finite. Let $K$ be a field extension of $K_0$ carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$. Three compatibility hypotheses are imposed: $v$ takes values $\le 1$ on the image of $R$ in $K$; conversely every $a \in K_0$ whose image in $K$ has $v(a) \le 1$ is an $R$-integer, i.e. lies in the image of $R$; and for every $\varepsilon \in \Gamma_0$ with $\varepsilon \ne 0$ there is $N \in \mathbb{N}$ with $v(\varpi)^N \le \varepsilon$. Let $G$ be a group and $\rho \colon G \to \mathrm{PGL}_2(K_0)$ a group homomorphism, and suppose that the set of $\gamma \in G$ with $\rho(\gamma)$ fixing the standard vertex $\mathrm{stdVertex}\,R\,K_0$ — the homothety class of the lattice of vectors in $K_0^2$ both of whose coordinates are $R$-integers — is finite. Then $\rho$ satisfies [`CerednikDrinfeld.Omega.IsDiscrete`](def/CerednikDrinfeld_DiscreteProjectiveAction.html#L10): for every $\varepsilon \in \Gamma_0$ with $\varepsilon \ne 0$, the set of $\gamma \in G$ admitting a representative $g \in \mathrm{GL}_2(K_0)$ of $\rho(\gamma)$ with $v(g_{ij}) \le 1$ for all $i,j$ and $\varepsilon \le v(\det g)$ is finite.
--
--   This is the standard criterion identifying groups acting on the Bruhat–Tits tree of $\mathrm{PGL}_2$ over a local field with finite vertex stabilisers (tree lattices, Schottky groups) as discrete subgroups in the valuation-theoretic sense used for the Drinfeld upper half-plane. It supplies the discreteness input for the Čerednik–Drinfeld-style results on Mumford quotients, in particular the statements about $\mathrm{Pic}^0$ and period data for Mumford curves that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_isDiscrete_of_finite_stabilizer_stdVertex.lean

import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem CerednikDrinfeld.Omega.isDiscrete_of_finite_stabilizer_stdVertex
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    (hst : {γ : G | ρ γ • LT.LatticeTree.stdVertex R K₀ = LT.LatticeTree.stdVertex R K₀}.Finite) :
    CerednikDrinfeld.Omega.IsDiscrete K ρ := by sorry
