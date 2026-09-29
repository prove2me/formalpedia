-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_exists_eq_prod_pow_of_forall_mem_stabilizer_of_forall_exists_pow_eq
-- name    : CerednikDrinfeld.Mumford.exists_eq_prod_pow_of_forall_mem_stabilizer_of_forall_exists_pow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/91bdc8bd-ad37-561d-a263-eed28f1f8456
-- title:
--   Vanishing on stabilisers: c as a product of cycle-vector powers
-- statement:
--   Let $G$ be a group acting on a set $W$, let $\mathcal T$ be a simple graph on $W$ whose adjacency is preserved by the action, and assume $\mathcal T$ is a tree. Let $\tau : W \to \mathbb Z/2$ be a $G$-invariant function taking different values at adjacent vertices. Let $E$ be a finite type, $V$ a type with decidable equality, and $D$ a degeneracy datum on $(E,V)$, i.e. maps $a, b : E \to V$ together with weights $E \to \mathbb Z_{>0}$. Assume given bijections $eE$ between $E$ and the set of $G$-orbits of darts of $\mathcal T$ whose chosen representative has source of $\tau$-value $0$, and $eV$ between $V$ and the set of $G$-orbits of $W$, compatible with $D$ in the sense that $eV(a(e))$ and $eV(b(e))$ are the orbits of the source and the target of the representative dart of $eE(e)$. Fix a base vertex $v_0 \in W$ and an additive homomorphism $\Phi$ from the abelianisation of $G$ (written additively) to the submodule $\mathrm{ribbonKernel}\,D \subseteq \mathbb Z^E$ cut out by the two pushforward maps along $a$ and along $b$, such that for every $g$ the vector $\Phi([g])$ is the cycle vector `pathCycle` of a chosen path from $v_0$ to $g \cdot v_0$, counted in each edge orbit. Let $A$ be a commutative group in which every element admits an $n$-th root for every $n \neq 0$, and let $c : G \to A$ be a homomorphism with $c(g) = 1$ whenever $g$ stabilises some vertex $w \in W$. Then there is a family $\nu : E \to A$ with $c(g) = \prod_{e \in E} \nu(e)^{\Phi([g])_e}$ for all $g \in G$.
--
--   This is the step which turns a character of a tree lattice that is trivial on all vertex stabilisers into an explicit multiplicative expression in the cycle-vector coordinates, the coordinates being indexed by the edge orbits of the quotient graph. It is used in the construction of the multiplicative periods attached to the Čerednik–Drinfeld uniformisation, where $A$ is a divisible value group and $c$ the absolute value of a character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_exists_eq_prod_pow_of_forall_mem_stabilizer_of_forall_exists_pow_eq.lean

import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Mathlib.GroupTheory.Abelianization.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Mumford.exists_eq_prod_pow_of_forall_mem_stabilizer_of_forall_exists_pow_eq
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hT : 𝒯.IsTree)
    (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
    [DecidableEq (QuotEdge G 𝒯)]
    {E V : Type} [Fintype E] [DecidableEq V] (D : DegeneracyData E V)
    (eE : E ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0})
    (eV : V ≃ QuotVert G W)
    (ha : ∀ e : E, eV (D.a e) = Quotient.mk (orbitRel G W) (eE e).1.out.fst)
    (hb : ∀ e : E, eV (D.b e) = Quotient.mk (orbitRel G W) (eE e).1.out.snd)
    (v₀ : W)
    (Φ : Additive (Abelianization G) →+ ↥(ribbonKernel D))
    (hΦ : ∀ g : G, (Φ (Additive.ofMul (Abelianization.of g)) : E → ℤ) = pathCycle 𝒯 (fun e => (eE e).1) v₀ g)
    (A : Type) [CommGroup A] (hdiv : ∀ (a : A) (n : ℕ), n ≠ 0 → ∃ b : A, b ^ n = a)
    (c : G →* A) (hc : ∀ (w : W) (g : G), g ∈ stabilizer G w → c g = 1) :
    ∃ ν : E → A, ∀ g : G, c g = ∏ e : E, ν e ^ ((Φ (Additive.ofMul (Abelianization.of g)) : E → ℤ) e) := by sorry
