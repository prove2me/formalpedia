-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_countable_of_isDiscrete
-- name    : CerednikDrinfeld.Omega.countable_of_isDiscrete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/7568f560-efab-5b39-870a-5dbc95b174f6
-- title:
--   Discreteness in the valuation sense forces G countable
-- statement:
--   Let $K_0$ be a field and $K$ a field equipped with a $K_0$-algebra structure and a valuation $v =$ `Valued.v` taking values in a linearly ordered commutative group with zero $\Gamma_0$. Let $\varpi$ be a pseudo-uniformiser for $K_0 \to K$, that is, an element $\varpi \in K_0$ such that $0 < v(\varpi) < 1$ in $\Gamma_0$ (valuations of images under $\mathrm{alg}: K_0 \to K$ throughout) and such that for every nonzero $a \in K_0$ there is an $N \in \mathbb{N}$ with $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$. Let $G$ be a group and $\rho : G \to \mathrm{PGL}_2(K_0)$ a group homomorphism satisfying `IsDiscrete K ρ`, i.e. for every $\varepsilon \in \Gamma_0$ with $\varepsilon \ne 0$ the set of those $\gamma \in G$ for which some $g \in \mathrm{GL}_2(K_0)$ has image $\rho(\gamma)$ in $\mathrm{PGL}_2(K_0)$, all four entries of valuation $\le 1$, and $v(\det g) \ge \varepsilon$, is finite. Then $G$ is countable. No injectivity of $\rho$ is assumed.
--
--   This is the valuation-theoretic counterpart of the statement that a discrete subgroup of $\mathrm{PGL}_2$ over a local field is countable; it supplies the countability needed to form countable unions and products in the Čerednik–Drinfeld setting, and is used in the study of orbits on the Drinfeld upper half plane and of Mumford quotients, for instance in the construction of holomorphic functions with prescribed orders along orbits and in the resulting statements about degree-zero Picard groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_countable_of_isDiscrete.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.countable_of_isDiscrete
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ) :
    Countable G := by sorry
